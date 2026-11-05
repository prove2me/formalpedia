-- Prove2me | solution 1 for SlottingFees.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T15:20:44.868908+00:00
-- url     : https://prove2.me/submissions/7880e947-1181-4d54-b91b-75951d3fcc40

import Definitions.Def_SlottingFees_Game
import Definitions.Def_SlottingFees_Regions

/-!
# Proposition 5 of Alan–Kurtuluş–Nakkas (slotting fees)

Full backward-induction solution of both subgames:
* `|A| = 1`: retail pricing, upstream monopoly / zero-profit / competitive prices and the
  retailer's fee choice (value `L - K` with fees, `M - K` without, product `idxR`);
* `|A| = 2`: retail pricing via a strictly concave quantity problem, uniqueness of the
  wholesale Nash equilibrium (interior on `Ω`), and the closed forms `v12`, `S2`.
-/

open MeasureTheory

namespace SlottingFees
namespace P5

lemma sq_le_zero_eq {a b : ℝ} (h : (a - b) ^ 2 ≤ 0) : a = b := by
  have h2 : (a - b) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  linarith

/-! ## Single-product facts -/

noncomputable def G1f (ω : Params) (l : Fin 2) (w : ℝ) : ℝ :=
  (max 0 (ω.q l - w)) ^ 2 / (4 * ω.q l)

noncomputable def m1f (ω : Params) (l : Fin 2) (w : ℝ) : ℝ :=
  (w - ω.c l) * max 0 (ω.q l - w) / (2 * ω.q l)

lemma demand_single (ω : Params) (i : Fin 2) (p : ℝ) (hq : 0 < ω.q i) (h0 : 0 ≤ p)
    (hpq : p ≤ ω.q i) : demand ω {i} (fun _ => p) i = 1 - p / ω.q i := by
  unfold demand
  rw [if_pos (Finset.mem_singleton_self i)]
  have hset : {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ * ω.q i - (fun _ => p) i ∧
      ∀ j ∈ ({i} : Finset (Fin 2)), θ * ω.q j - (fun _ => p) j ≤ θ * ω.q i - (fun _ => p) i}
      = Set.Icc (p / ω.q i) 1 := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Finset.mem_singleton, forall_eq, le_refl, and_true]
    rw [div_le_iff₀ hq]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h2⟩, by linarith⟩
      by_contra h; push Not at h
      nlinarith
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal]
  rw [sub_nonneg, div_le_one hq]; exact hpq

lemma gross1_eq (ω : Params) (i : Fin 2) (w p : ℝ) (hq : 0 < ω.q i) (h0 : 0 ≤ p)
    (hpq : p ≤ ω.q i) : gross1 ω i w p = (p - w) * (ω.q i - p) / ω.q i := by
  unfold gross1 grossProfit
  rw [Finset.sum_singleton, demand_single ω i p hq h0 hpq]
  field_simp

lemma gross1_le (ω : Params) (i : Fin 2) (w p : ℝ) (hq : 0 < ω.q i) (hw : 0 ≤ w) (h0 : 0 ≤ p)
    (hpq : p ≤ ω.q i) : gross1 ω i w p + (if w ≤ ω.q i then (p - (ω.q i + w) / 2) ^ 2 / ω.q i
      else 0) ≤ G1f ω i w := by
  rw [gross1_eq ω i w p hq h0 hpq]
  unfold G1f
  split_ifs with h
  · rw [max_eq_right (by linarith)]
    rw [div_add_div _ _ hq.ne' hq.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf; nlinarith [sq_nonneg (p - (ω.q i + w) / 2)]
  · push Not at h
    rw [max_eq_left (by linarith), add_zero]
    have : (p - w) * (ω.q i - p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have : (p - w) * (ω.q i - p) / ω.q i ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hq.le
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]; linarith

noncomputable def pstar (ω : Params) (i : Fin 2) (w : ℝ) : ℝ := min (ω.q i) ((ω.q i + w) / 2)

lemma pstar_mem (ω : Params) (i : Fin 2) (w : ℝ) (hq : 0 < ω.q i) (hw : 0 ≤ w) :
    pstar ω i w ∈ Set.Icc 0 (ω.q i) :=
  ⟨le_min hq.le (by linarith), min_le_left _ _⟩

lemma gross1_pstar (ω : Params) (i : Fin 2) (w : ℝ) (hq : 0 < ω.q i) (hw : 0 ≤ w) :
    gross1 ω i w (pstar ω i w) = G1f ω i w := by
  have hm := pstar_mem ω i w hq hw
  rw [gross1_eq ω i w _ hq hm.1 hm.2]
  unfold G1f pstar
  rcases le_total w (ω.q i) with h | h
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    field_simp; ring
  · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
    simp

lemma optGross1_eq (ω : Params) (i : Fin 2) (w : ℝ) (hq : 0 < ω.q i) (hw : 0 ≤ w) :
    optGross1 ω i w = G1f ω i w := by
  unfold optGross1
  apply IsGreatest.csSup_eq
  refine ⟨⟨pstar ω i w, pstar_mem ω i w hq hw, gross1_pstar ω i w hq hw⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have := gross1_le ω i w p hq hw hp.1 hp.2
  have : 0 ≤ (if w ≤ ω.q i then (p - (ω.q i + w) / 2) ^ 2 / ω.q i else 0) := by
    split_ifs <;> positivity
  linarith

lemma optPrice1_eq (ω : Params) (i : Fin 2) (w p : ℝ) (hq : 0 < ω.q i) (hw : 0 ≤ w)
    (h : IsOptPrice1 ω i w p) : p = pstar ω i w := by
  obtain ⟨hp, hmax⟩ := h
  have h1 := hmax _ (pstar_mem ω i w hq hw)
  rw [gross1_pstar ω i w hq hw] at h1
  have h2 := gross1_le ω i w p hq hw hp.1 hp.2
  unfold pstar
  split_ifs at h2 with hwq
  · rw [min_eq_right (by linarith)]
    have : (p - (ω.q i + w) / 2) ^ 2 / ω.q i ≤ 0 := by linarith
    have : (p - (ω.q i + w) / 2) ^ 2 ≤ 0 := by
      by_contra hc
      have := div_pos (not_le.mp hc) hq
      linarith
    exact sq_le_zero_eq this
  · push Not at hwq
    rw [min_eq_left (by linarith)]
    rw [gross1_eq ω i w p hq hp.1 hp.2] at h1
    unfold G1f at h1
    rw [max_eq_left (by linarith)] at h1
    simp at h1
    rw [le_div_iff₀ hq] at h1
    simp at h1
    nlinarith [hp.2]

def Good (ω : Params) : Prop := ∀ l : Fin 2, 0 ≤ ω.c l ∧ ω.c l < ω.q l

section single
variable (ω : Params) (hG : Good ω)
include hG

lemma hq_pos (l : Fin 2) : 0 < ω.q l := by have := hG l; linarith

lemma price1_eq {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {l : Fin 2} {w : ℝ}
    (hc : ω.c l ≤ w) : σ l w = pstar ω l w :=
  optPrice1_eq ω l w _ (hq_pos ω hG l) (le_trans (hG l).1 hc) (hσ l w hc)

lemma mfrGross1_eq {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {l : Fin 2} {w : ℝ}
    (hc : ω.c l ≤ w) : mfrGross1 ω σ l w = m1f ω l w := by
  have hq := hq_pos ω hG l
  have hm := pstar_mem ω l w hq (le_trans (hG l).1 hc)
  unfold mfrGross1 mfrGross
  rw [price1_eq ω hG hσ hc, demand_single ω l _ hq hm.1 hm.2]
  unfold m1f pstar
  rcases le_total w (ω.q l) with h | h
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    field_simp; ring
  · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp; simp

lemma payoff1_some {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {i : Fin 2} {w : ℝ} (S : ℝ)
    (hc : ω.c i ≤ w) : payoff1 ω σ S (some (i, w)) = G1f ω i w + S - ω.K := by
  show retailerProfit ω {i} (fun _ => w) (fun _ => σ i w) S = _
  unfold retailerProfit
  have : grossProfit ω {i} (fun _ => w) (fun _ => σ i w) = gross1 ω i w (σ i w) := rfl
  rw [this, price1_eq ω hG hσ hc, gross1_pstar ω i w (hq_pos ω hG i) (le_trans (hG i).1 hc)]
  simp

lemma m1f_le {l : Fin 2} {w : ℝ} (hc : ω.c l ≤ w) : m1f ω l w ≤ ω.v l / 8 := by
  have hq := hq_pos ω hG l
  unfold m1f Params.v
  rcases le_total w (ω.q l) with h | h
  · rw [max_eq_right (by linarith), div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (w - (ω.q l + ω.c l) / 2)]
  · rw [max_eq_left (by linarith)]; simp; positivity

lemma m1f_top {l : Fin 2} {w : ℝ} (hc : ω.c l ≤ w) (h : ω.v l / 8 ≤ m1f ω l w) :
    w = (ω.q l + ω.c l) / 2 := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold m1f Params.v at h
  rcases le_total w (ω.q l) with h' | h'
  · rw [max_eq_right (by linarith), div_div, div_le_div_iff₀ (by positivity) (by positivity)] at h
    have e : (w - ω.c l) * (ω.q l - w) = (ω.q l - ω.c l) ^ 2 / 4 - (w - (ω.q l + ω.c l) / 2) ^ 2 := by
      ring
    rw [e] at h
    have h3 : ω.q l * (w - (ω.q l + ω.c l) / 2) ^ 2 ≤ 0 := by linarith
    have h4 : (w - (ω.q l + ω.c l) / 2) ^ 2 ≤ 0 := by
      by_contra hc'; have := mul_pos hq (not_le.mp hc'); linarith
    exact sq_le_zero_eq h4
  · rw [max_eq_left (by linarith)] at h; simp at h
    have : 0 < (ω.q l - ω.c l) ^ 2 / ω.q l / 8 := by
      have : 0 < ω.q l - ω.c l := by linarith
      positivity
    linarith

lemma m1f_wm (l : Fin 2) : m1f ω l ((ω.q l + ω.c l) / 2) = ω.v l / 8 := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold m1f Params.v
  rw [max_eq_right (by linarith)]
  field_simp; ring

lemma m1f_lt {l : Fin 2} {x y : ℝ} (hc : ω.c l ≤ x) (hxy : x < y)
    (hy : y ≤ (ω.q l + ω.c l) / 2) : m1f ω l x < m1f ω l y := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold m1f
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  nlinarith

lemma m1f_nonneg {l : Fin 2} {w : ℝ} (hc : ω.c l ≤ w) : 0 ≤ m1f ω l w := by
  have hq := hq_pos ω hG l
  unfold m1f
  apply div_nonneg _ (by positivity)
  exact mul_nonneg (by linarith) (le_max_left _ _)

lemma G1f_anti {l : Fin 2} {x y : ℝ} (hxy : x ≤ y) : G1f ω l y ≤ G1f ω l x := by
  have hq := hq_pos ω hG l
  unfold G1f
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (le_max_left _ _)
  exact max_le_max le_rfl (by linarith)

lemma G1f_nonneg (l : Fin 2) (x : ℝ) : 0 ≤ G1f ω l x := by
  have hq := hq_pos ω hG l
  unfold G1f; positivity

lemma G1f_c (l : Fin 2) : G1f ω l (ω.c l) = ω.v l / 4 := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold G1f Params.v
  rw [max_eq_right (by linarith)]
  field_simp

lemma G1f_wm (l : Fin 2) : G1f ω l ((ω.q l + ω.c l) / 2) = ω.v l / 16 := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold G1f Params.v
  rw [max_eq_right (by linarith)]
  field_simp; ring

lemma v_pos (l : Fin 2) : 0 < ω.v l := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  unfold Params.v
  have : 0 < ω.q l - ω.c l := by linarith
  positivity

lemma canAfford_iff {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (l : Fin 2) (S : ℝ) :
    CanAfford ω σ l S ↔ S ≤ ω.v l / 8 := by
  constructor
  · rintro ⟨w, hc, h⟩
    rw [mfrGross1_eq ω hG hσ hc] at h
    have := m1f_le ω hG hc; linarith
  · intro h
    have hc : ω.c l ≤ (ω.q l + ω.c l) / 2 := by have := (hG l).2; linarith
    refine ⟨_, hc, ?_⟩
    rw [mfrGross1_eq ω hG hσ hc, m1f_wm ω hG]; linarith

lemma zp_facts {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {l : Fin 2} {S w : ℝ}
    (hS0 : 0 ≤ S) (h : IsZeroProfitPrice ω σ l S w) :
    ω.c l ≤ w ∧ G1f ω l w + S ≤ ω.v l / 4 ∧ (G1f ω l w + S = ω.v l / 4 → S = 0) ∧
      (S = 0 → w = ω.c l) := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  obtain ⟨⟨hc, hS⟩, hleast⟩ := h
  rw [mfrGross1_eq ω hG hσ hc] at hS
  have hS8 : S ≤ ω.v l / 8 := by have := m1f_le ω hG hc; linarith
  have hwm : w ≤ (ω.q l + ω.c l) / 2 := by
    apply hleast
    refine ⟨by linarith, ?_⟩
    rw [mfrGross1_eq ω hG hσ (by linarith), m1f_wm ω hG]; linarith
  have key : G1f ω l w + S ≤ ω.v l / 4 - (w - ω.c l) ^ 2 / (4 * ω.q l) := by
    unfold m1f at hS
    unfold G1f Params.v
    rw [max_eq_right (by linarith)] at hS ⊢
    have : S ≤ (w - ω.c l) * (ω.q l - w) / (2 * ω.q l) := by linarith
    have e : (ω.q l - ω.c l) ^ 2 / ω.q l / 4 - (w - ω.c l) ^ 2 / (4 * ω.q l)
        - (ω.q l - w) ^ 2 / (4 * ω.q l) = (w - ω.c l) * (ω.q l - w) / (2 * ω.q l) := by
      field_simp; ring
    linarith
  refine ⟨hc, ?_, ?_, ?_⟩
  · have : 0 ≤ (w - ω.c l) ^ 2 / (4 * ω.q l) := by positivity
    linarith
  · intro heq
    have h1 : (w - ω.c l) ^ 2 / (4 * ω.q l) ≤ 0 := by linarith
    have h2 : (w - ω.c l) ^ 2 ≤ 0 := by
      by_contra hc'; have := div_pos (not_le.mp hc') (by positivity : (0:ℝ) < 4 * ω.q l)
      linarith
    have hw : w = ω.c l := sq_le_zero_eq h2
    have : m1f ω l w = 0 := by rw [hw]; unfold m1f; simp
    linarith
  · intro hS00
    have := hleast (show ω.c l ∈ {x | ω.c l ≤ x ∧ 0 ≤ mfrGross1 ω σ l x - S} from by
      refine ⟨le_rfl, ?_⟩
      rw [mfrGross1_eq ω hG hσ le_rfl, hS00]; unfold m1f; simp)
    linarith

lemma zp_exists {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (l : Fin 2) {S : ℝ}
    (hS : S ≤ ω.v l / 8) : ∃ w, IsZeroProfitPrice ω σ l S w := by
  have hq := hq_pos ω hG l
  have hcq := (hG l).2
  set T := {x | ω.c l ≤ x ∧ 0 ≤ mfrGross1 ω σ l x - S} with hT
  have hT' : T = {x | ω.c l ≤ x ∧ S ≤ m1f ω l x} := by
    ext x; simp only [hT, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; rw [mfrGross1_eq ω hG hσ h1] at h2; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; rw [mfrGross1_eq ω hG hσ h1]; exact ⟨h1, by linarith⟩
  have hcl : IsClosed T := by
    rw [hT']
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (show Continuous (fun x => m1f ω l x) by unfold m1f; fun_prop))
  have hne : T.Nonempty := by
    refine ⟨(ω.q l + ω.c l) / 2, ?_⟩
    rw [hT']; exact ⟨by linarith, by rw [m1f_wm ω hG]; exact hS⟩
  have hbdd : BddBelow T := ⟨ω.c l, fun x hx => hx.1⟩
  exact ⟨sInf T, hcl.csInf_mem hne hbdd, fun x hx => csInf_le hbdd hx⟩

lemma mono_eq {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {l : Fin 2} {S w : ℝ}
    (h : IsMonopolyPrice ω σ l S w) : w = (ω.q l + ω.c l) / 2 := by
  obtain ⟨hc, hmax⟩ := h
  have hcq := (hG l).2
  have := hmax ((ω.q l + ω.c l) / 2) (by linarith)
  rw [mfrGross1_eq ω hG hσ hc, mfrGross1_eq ω hG hσ (by linarith), m1f_wm ω hG] at this
  exact m1f_top ω hG hc (by linarith)

lemma mono_exists {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (l : Fin 2) (S : ℝ) :
    IsMonopolyPrice ω σ l S ((ω.q l + ω.c l) / 2) := by
  have hcq := (hG l).2
  refine ⟨by linarith, fun x hx => ?_⟩
  rw [mfrGross1_eq ω hG hσ hx, mfrGross1_eq ω hG hσ (by linarith), m1f_wm ω hG]
  have := m1f_le ω hG hx; linarith

lemma comp_facts {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {i : Fin 2} {wj S w : ℝ}
    (hwj : 0 ≤ wj) (h : IsCompetitivePrice ω σ i wj S w) :
    G1f ω (other i) wj ≤ G1f ω i w ∧ ω.v i / 16 ≤ G1f ω i w ∧
      G1f ω i w ≤ max (G1f ω (other i) wj) (ω.v i / 16) := by
  have hq := hq_pos ω hG i
  have hcq := (hG i).2
  have hc0 := (hG i).1
  obtain ⟨hc, hcon, hmax⟩ := h
  rw [optGross1_eq ω _ wj (hq_pos ω hG _) hwj, optGross1_eq ω i w hq (by linarith)] at hcon
  set R := G1f ω (other i) wj with hR
  have hR0 : 0 ≤ R := G1f_nonneg ω hG _ _
  set wm := (ω.q i + ω.c i) / 2 with hwm
  have hmax' : ∀ x, ω.c i ≤ x → R ≤ G1f ω i x → m1f ω i x ≤ m1f ω i w := by
    intro x hx hRx
    have := hmax x hx (by rw [optGross1_eq ω _ wj (hq_pos ω hG _) hwj,
      optGross1_eq ω i x hq (by linarith)]; exact hRx)
    rw [mfrGross1_eq ω hG hσ hx, mfrGross1_eq ω hG hσ hc] at this; linarith
  have hwle : w ≤ wm := by
    by_contra hlt; push Not at hlt
    have h1 := hmax' wm (by linarith) (le_trans hcon (G1f_anti ω hG hlt.le))
    rw [m1f_wm ω hG] at h1
    have := m1f_top ω hG hc h1
    linarith
  refine ⟨hcon, ?_, ?_⟩
  · rw [← G1f_wm ω hG]; exact G1f_anti ω hG hwle
  · by_contra hgt; push Not at hgt
    have hgt1 : R < G1f ω i w := lt_of_le_of_lt (le_max_left _ _) hgt
    have hgt2 : ω.v i / 16 < G1f ω i w := lt_of_le_of_lt (le_max_right _ _) hgt
    have hwlt : w < wm := by
      rcases lt_or_eq_of_le hwle with h | h
      · exact h
      · rw [h, G1f_wm ω hG] at hgt2; linarith
    set xb := ω.q i - Real.sqrt (4 * ω.q i * R) with hxb
    have hsq := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * ω.q i * R)
    have hs0 := Real.sqrt_nonneg (4 * ω.q i * R)
    have hwxb : w < xb := by
      unfold G1f at hgt1
      rw [max_eq_right (by linarith), lt_div_iff₀ (by positivity)] at hgt1
      have : Real.sqrt (4 * ω.q i * R) < ω.q i - w := by
        rw [Real.sqrt_lt' (by linarith)]; linarith
      linarith
    set x := min xb wm with hx
    have hxw : w < x := lt_min hwxb hwlt
    have hRx : R ≤ G1f ω i x := by
      unfold G1f
      have hxq : x ≤ xb := min_le_left _ _
      rw [max_eq_right (by linarith), le_div_iff₀ (by positivity)]
      nlinarith
    have h1 := hmax' x (by linarith) hRx
    have h2 := m1f_lt ω hG hc hxw (min_le_right _ _)
    linarith

lemma comp_exists {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (i : Fin 2) {wj : ℝ} (S : ℝ)
    (hwj : 0 ≤ wj) (hR : G1f ω (other i) wj ≤ ω.v i / 4) :
    ∃ w, IsCompetitivePrice ω σ i wj S w := by
  have hq := hq_pos ω hG i
  have hcq := (hG i).2
  have hc0 := (hG i).1
  set R := G1f ω (other i) wj with hRdef
  have hR0 : 0 ≤ R := G1f_nonneg ω hG _ _
  set wm := (ω.q i + ω.c i) / 2 with hwm
  set xb := ω.q i - Real.sqrt (4 * ω.q i * R) with hxb
  have hsq := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * ω.q i * R)
  have hs0 := Real.sqrt_nonneg (4 * ω.q i * R)
  have hxbc : ω.c i ≤ xb := by
    have : Real.sqrt (4 * ω.q i * R) ≤ ω.q i - ω.c i := by
      rw [Real.sqrt_le_left (by linarith)]
      unfold Params.v at hR
      rw [div_div, le_div_iff₀ (by positivity)] at hR
      nlinarith
    linarith
  refine ⟨min xb wm, le_min hxbc (by linarith), ?_, ?_⟩
  · rw [optGross1_eq ω _ wj (hq_pos ω hG _) hwj, optGross1_eq ω i _ hq
      (le_trans hc0 (le_min hxbc (by linarith)))]
    rw [← hRdef]
    unfold G1f
    have hxq : min xb wm ≤ xb := min_le_left _ _
    rw [max_eq_right (by linarith), le_div_iff₀ (by positivity)]
    nlinarith
  · intro x hx hcon
    rw [optGross1_eq ω _ wj (hq_pos ω hG _) hwj, optGross1_eq ω i x hq (by linarith),
      ← hRdef] at hcon
    rw [mfrGross1_eq ω hG hσ hx, mfrGross1_eq ω hG hσ (le_min hxbc (by linarith))]
    suffices m1f ω i x ≤ m1f ω i (min xb wm) by linarith
    rcases le_total xb wm with hb | hb
    · rw [min_eq_left hb]
      rcases le_or_gt x xb with hxx | hxx
      · rcases lt_or_eq_of_le hxx with h | h
        · exact (m1f_lt ω hG hx h hb).le
        · rw [h]
      · -- x > xb : then constraint fails unless R = 0 and x ≥ q
        exfalso
        unfold G1f at hcon
        rcases le_total x (ω.q i) with hxq | hxq
        · rw [max_eq_right (by linarith), le_div_iff₀ (by positivity)] at hcon
          nlinarith
        · rw [max_eq_left (by linarith)] at hcon
          simp at hcon
          have hR00 : R = 0 := le_antisymm (by linarith) hR0
          rw [hR00] at hxb; simp at hxb
          linarith
    · rw [min_eq_right hb, m1f_wm ω hG]; exact m1f_le ω hG hx

end single

noncomputable def LvR (v0 v1 : ℝ) : ℝ :=
  if v1 ≤ v0 then max (3 * v0 / 16) (v1 / 4) else max (v0 / 4) (3 * v1 / 16)
noncomputable def MvR (v0 v1 : ℝ) : ℝ :=
  if v1 ≤ v0 then max (v0 / 16) (v1 / 4) else max (v0 / 4) (v1 / 16)
noncomputable def SoptR (v0 v1 : ℝ) : ℝ :=
  if v1 ≤ v0 then (if 3 * v0 / 16 ≤ v1 / 4 then 0 else v0 / 8)
  else (if 3 * v1 / 16 ≤ v0 / 4 then 0 else v1 / 8)
noncomputable def idxR (v0 v1 : ℝ) : Fin 2 := if v1 ≤ v0 then 0 else 1

lemma SoptR_nonneg (v0 v1 : ℝ) (h0 : 0 < v0) (h1 : 0 < v1) : 0 ≤ SoptR v0 v1 := by
  unfold SoptR; split_ifs <;> linarith

lemma both_bound (v0 v1 R0 R1 S G : ℝ) (hv0 : 0 < v0) (hv1 : 0 < v1) (hS : 0 ≤ S)
    (hS0 : S ≤ v0 / 8) (hS1 : S ≤ v1 / 8) (hR0 : R0 + S ≤ v0 / 4) (hR1 : R1 + S ≤ v1 / 4)
    (hE0 : R0 + S = v0 / 4 → S = 0) (hE1 : R1 + S = v1 / 4 → S = 0)
    (hG : (R1 ≤ R0 ∧ G ≤ max R1 (v0 / 16)) ∨ (R0 ≤ R1 ∧ G ≤ max R0 (v1 / 16))) :
    G + S ≤ LvR v0 v1 ∧ (G + S = LvR v0 v1 → S = 0 ∧ SoptR v0 v1 = 0) := by
  unfold LvR SoptR
  by_cases hv : v1 ≤ v0
  · simp only [hv, if_true]
    by_cases hm : 3 * v0 / 16 ≤ v1 / 4
    · simp only [hm, if_true, max_eq_right hm]
      rcases hG with ⟨hRR, hGl⟩ | ⟨hRR, hGl⟩ <;> rcases le_max_iff.mp hGl with h | h <;>
        exact ⟨by linarith, fun he => ⟨hE1 (by linarith), by simp⟩⟩
    · simp only [hm, if_false]
      push Not at hm
      rw [max_eq_left hm.le]
      rcases hG with ⟨hRR, hGl⟩ | ⟨hRR, hGl⟩ <;> rcases le_max_iff.mp hGl with h | h <;>
        exact ⟨by linarith, fun he => by exfalso; linarith⟩
  · simp only [hv, if_false]
    push Not at hv
    by_cases hm : 3 * v1 / 16 ≤ v0 / 4
    · simp only [hm, if_true, max_eq_left hm]
      rcases hG with ⟨hRR, hGl⟩ | ⟨hRR, hGl⟩ <;> rcases le_max_iff.mp hGl with h | h <;>
        exact ⟨by linarith, fun he => ⟨hE0 (by linarith), by simp⟩⟩
    · simp only [hm, if_false]
      push Not at hm
      rw [max_eq_right hm.le]
      rcases hG with ⟨hRR, hGl⟩ | ⟨hRR, hGl⟩ <;> rcases le_max_iff.mp hGl with h | h <;>
        exact ⟨by linarith, fun he => by exfalso; linarith⟩

lemma other0 : other 0 = 1 := rfl
lemma other1 : other 1 = 0 := rfl

section stage2
variable (ω : Params) (hG : Good ω)
include hG

lemma char1 {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {S : ℝ} (hS : 0 ≤ S)
    {o : Option (Fin 2 × ℝ)} (ho : IsStage2Outcome1 ω σ S o) {i : Fin 2} {w : ℝ}
    (hio : o = some (i, w)) :
    payoff1 ω σ S o ≤ LvR (ω.v 0) (ω.v 1) - ω.K ∧
      (payoff1 ω σ S o = LvR (ω.v 0) (ω.v 1) - ω.K →
        i = idxR (ω.v 0) (ω.v 1) ∧ SoptR (ω.v 0) (ω.v 1) ≤ S) := by
  obtain ⟨hn, h2, h3⟩ := ho
  have hv0 := v_pos ω hG 0
  have hv1 := v_pos ω hG 1
  have hA := canAfford_iff ω hG hσ
  by_cases h0 : CanAfford ω σ 0 S <;> by_cases h1 : CanAfford ω σ 1 S
  · obtain ⟨w0, hw0, i', w', ho', hiff, hcomp⟩ := h3 h0 h1
    rw [hio] at ho'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
    have z0 := zp_facts ω hG hσ hS (hw0 0)
    have z1 := zp_facts ω hG hσ hS (hw0 1)
    have hc0 := (hG 0).1
    have hc1 := (hG 1).1
    rw [optGross1_eq ω 1 _ (hq_pos ω hG 1) (by linarith [z1.1]),
      optGross1_eq ω 0 _ (hq_pos ω hG 0) (by linarith [z0.1])] at hiff
    rw [hA] at h0 h1
    have hcw : ω.c i ≤ w := hcomp.1
    rw [hio, payoff1_some ω hG hσ S hcw]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have hf := comp_facts ω hG hσ (by rw [other0]; linarith [z1.1]) hcomp
      simp only [other0] at hf
      have hRR := hiff.mp rfl
      have hb := both_bound (ω.v 0) (ω.v 1) (G1f ω 0 (w0 0)) (G1f ω 1 (w0 1)) S (G1f ω 0 w) hv0 hv1
        hS h0 h1 z0.2.1 z1.2.1 z0.2.2.1 z1.2.2.1 (Or.inl ⟨hRR, hf.2.2⟩)
      refine ⟨by linarith [hb.1], fun he => ?_⟩
      have hb2 := hb.2 (by linarith)
      refine ⟨?_, by rw [hb2.2]; exact hS⟩
      have e0 := z0.2.2.2 hb2.1
      have e1 := z1.2.2.2 hb2.1
      rw [e0, e1, G1f_c ω hG, G1f_c ω hG] at hRR
      unfold idxR; rw [if_pos (by linarith)]
    · have hf := comp_facts ω hG hσ (by rw [other1]; linarith [z0.1]) hcomp
      simp only [other1] at hf
      have hRR : ¬ G1f ω 1 (w0 1) ≤ G1f ω 0 (w0 0) := fun h => absurd (hiff.mpr h) (by decide)
      push Not at hRR
      have hb := both_bound (ω.v 0) (ω.v 1) (G1f ω 0 (w0 0)) (G1f ω 1 (w0 1)) S (G1f ω 1 w) hv0 hv1
        hS h0 h1 z0.2.1 z1.2.1 z0.2.2.1 z1.2.2.1 (Or.inr ⟨hRR.le, hf.2.2⟩)
      refine ⟨by linarith [hb.1], fun he => ?_⟩
      have hb2 := hb.2 (by linarith)
      refine ⟨?_, by rw [hb2.2]; exact hS⟩
      have e0 := z0.2.2.2 hb2.1
      have e1 := z1.2.2.2 hb2.1
      rw [e0, e1, G1f_c ω hG, G1f_c ω hG] at hRR
      unfold idxR; rw [if_neg (by linarith)]
  · obtain ⟨w', ho', hm⟩ := h2 0 h0 (by rw [other0]; exact h1)
    rw [hio] at ho'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
    have hw := mono_eq ω hG hσ hm
    rw [hA] at h0 h1
    push Not at h1
    have hcq := (hG 0).2
    rw [hio, payoff1_some ω hG hσ S (by rw [hw]; linarith), hw, G1f_wm ω hG]
    have hv : ω.v 1 ≤ ω.v 0 := by linarith
    unfold LvR idxR SoptR
    simp only [hv, if_true]
    refine ⟨by linarith [le_max_left (3 * ω.v 0 / 16) (ω.v 1 / 4)], fun he => ⟨by simp, ?_⟩⟩
    have : ω.v 0 / 8 ≤ S := by linarith [le_max_left (3 * ω.v 0 / 16) (ω.v 1 / 4)]
    split_ifs <;> linarith
  · obtain ⟨w', ho', hm⟩ := h2 1 h1 (by rw [other1]; exact h0)
    rw [hio] at ho'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
    have hw := mono_eq ω hG hσ hm
    rw [hA] at h0 h1
    push Not at h0
    have hcq := (hG 1).2
    rw [hio, payoff1_some ω hG hσ S (by rw [hw]; linarith), hw, G1f_wm ω hG]
    have hv : ¬ ω.v 1 ≤ ω.v 0 := by intro h; linarith
    unfold LvR idxR SoptR
    simp only [hv, if_false]
    refine ⟨by linarith [le_max_right (ω.v 0 / 4) (3 * ω.v 1 / 16)], fun he => ⟨by simp, ?_⟩⟩
    have : ω.v 1 / 8 ≤ S := by linarith [le_max_right (ω.v 0 / 4) (3 * ω.v 1 / 16)]
    split_ifs <;> linarith
  · rw [hn h0 h1] at hio; exact absurd hio (by simp)

lemma att0 {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {o : Option (Fin 2 × ℝ)}
    (ho : IsStage2Outcome1 ω σ 0 o) :
    ∃ w, o = some (idxR (ω.v 0) (ω.v 1), w) ∧
      payoff1 ω σ 0 o = MvR (ω.v 0) (ω.v 1) - ω.K := by
  obtain ⟨_, _, h3⟩ := ho
  have hv0 := v_pos ω hG 0
  have hv1 := v_pos ω hG 1
  have hA := canAfford_iff ω hG hσ
  obtain ⟨w0, hw0, i, w, ho', hiff, hcomp⟩ :=
    h3 ((hA 0 0).mpr (by linarith)) ((hA 1 0).mpr (by linarith))
  have e0 := (zp_facts ω hG hσ le_rfl (hw0 0)).2.2.2 rfl
  have e1 := (zp_facts ω hG hσ le_rfl (hw0 1)).2.2.2 rfl
  have hc0 := (hG 0).1
  have hc1 := (hG 1).1
  rw [e0, e1, optGross1_eq ω 1 _ (hq_pos ω hG 1) hc1, optGross1_eq ω 0 _ (hq_pos ω hG 0) hc0,
    G1f_c ω hG, G1f_c ω hG] at hiff
  have hcw : ω.c i ≤ w := hcomp.1
  refine ⟨w, ?_, ?_⟩
  · rw [ho']; congr
    unfold idxR
    split_ifs with hv
    · exact hiff.mpr (by linarith)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exfalso; exact hv (by have := hiff.mp rfl; linarith)
      · rfl
  · rw [ho', payoff1_some ω hG hσ 0 hcw]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have hf := comp_facts ω hG hσ (by rw [other0, e1]; exact hc1) hcomp
      simp only [other0, e1, G1f_c ω hG] at hf
      have hv : ω.v 1 ≤ ω.v 0 := by have := hiff.mp rfl; linarith
      unfold MvR; simp only [hv, if_true]
      rw [max_comm]
      have := le_antisymm hf.2.2 (max_le hf.1 hf.2.1)
      linarith
    · have hf := comp_facts ω hG hσ (by rw [other1, e0]; exact hc0) hcomp
      simp only [other1, e0, G1f_c ω hG] at hf
      have hv : ¬ ω.v 1 ≤ ω.v 0 := by
        intro h; exact absurd (hiff.mpr (by linarith)) (by decide)
      unfold MvR; simp only [hv, if_false]
      have := le_antisymm hf.2.2 (max_le hf.1 hf.2.1)
      linarith

lemma attTop {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (l : Fin 2)
    (hlt : ω.v (other l) < ω.v l) {o : Option (Fin 2 × ℝ)}
    (ho : IsStage2Outcome1 ω σ (ω.v l / 8) o) :
    ∃ w, o = some (l, w) ∧ payoff1 ω σ (ω.v l / 8) o = 3 * ω.v l / 16 - ω.K := by
  obtain ⟨_, h2, _⟩ := ho
  have hA := canAfford_iff ω hG hσ
  obtain ⟨w, ho', hm⟩ := h2 l ((hA l _).mpr le_rfl) (by rw [hA]; intro h; linarith)
  have hw := mono_eq ω hG hσ hm
  have hcq := (hG l).2
  refine ⟨w, ho', ?_⟩
  rw [ho', payoff1_some ω hG hσ _ (by rw [hw]; linarith), hw, G1f_wm ω hG]
  ring

lemma exists_outcome1 {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) {S : ℝ} (hS : 0 ≤ S) :
    ∃ o, IsStage2Outcome1 ω σ S o := by
  have hA := canAfford_iff ω hG hσ
  by_cases h0 : CanAfford ω σ 0 S <;> by_cases h1 : CanAfford ω σ 1 S
  · have hl : ∀ l, S ≤ ω.v l / 8 := by
      intro l; fin_cases l
      · exact (hA 0 S).mp h0
      · exact (hA 1 S).mp h1
    have := fun l => zp_exists ω hG hσ l (hl l)
    choose w0 hw0 using this
    have z0 := zp_facts ω hG hσ hS (hw0 0)
    have z1 := zp_facts ω hG hσ hS (hw0 1)
    have hc0 := (hG 0).1
    have hc1 := (hG 1).1
    have g0 : 0 ≤ w0 0 := by linarith [z0.1]
    have g1 : 0 ≤ w0 1 := by linarith [z1.1]
    by_cases hc : optGross1 ω 1 (w0 1) ≤ optGross1 ω 0 (w0 0)
    · have hc' := hc
      rw [optGross1_eq ω 1 _ (hq_pos ω hG 1) g1, optGross1_eq ω 0 _ (hq_pos ω hG 0) g0] at hc'
      obtain ⟨w, hw⟩ := comp_exists ω hG hσ 0 S g1 (by
        rw [other0]; calc G1f ω 1 (w0 1) ≤ G1f ω 0 (w0 0) := hc'
          _ ≤ G1f ω 0 (ω.c 0) := G1f_anti ω hG z0.1
          _ = _ := G1f_c ω hG 0)
      refine ⟨some (0, w), fun h _ => absurd h0 h, fun i hi hni => ?_, fun _ _ =>
        ⟨w0, hw0, 0, w, rfl, ⟨fun _ => hc, fun _ => rfl⟩, hw⟩⟩
      fin_cases i
      · exact absurd h1 hni
      · exact absurd h0 hni
    · have hc' := hc
      rw [optGross1_eq ω 1 _ (hq_pos ω hG 1) g1, optGross1_eq ω 0 _ (hq_pos ω hG 0) g0] at hc'
      push Not at hc'
      obtain ⟨w, hw⟩ := comp_exists ω hG hσ 1 S g0 (by
        rw [other1]; calc G1f ω 0 (w0 0) ≤ G1f ω 1 (w0 1) := hc'.le
          _ ≤ G1f ω 1 (ω.c 1) := G1f_anti ω hG z1.1
          _ = _ := G1f_c ω hG 1)
      refine ⟨some (1, w), fun h _ => absurd h0 h, fun i hi hni => ?_, fun _ _ =>
        ⟨w0, hw0, 1, w, rfl, ⟨fun h => absurd h (by decide), fun h => absurd h hc⟩, hw⟩⟩
      fin_cases i
      · exact absurd h1 hni
      · exact absurd h0 hni
  · refine ⟨some (0, (ω.q 0 + ω.c 0) / 2), fun h _ => absurd h0 h, fun i hi hni => ?_,
      fun _ h => absurd h h1⟩
    fin_cases i
    · exact ⟨_, rfl, mono_exists ω hG hσ 0 S⟩
    · exact absurd hi h1
  · refine ⟨some (1, (ω.q 1 + ω.c 1) / 2), fun h _ => absurd h1 (by assumption), fun i hi hni => ?_,
      fun h _ => absurd h h0⟩
    fin_cases i
    · exact absurd hi h0
    · exact ⟨_, rfl, mono_exists ω hG hσ 1 S⟩
  · refine ⟨none, fun _ _ => rfl, fun i hi _ => ?_, fun h _ => absurd h h0⟩
    fin_cases i
    · exact absurd hi h0
    · exact absurd hi h1

omit hG in
lemma outcome_ne_none {σ : Fin 2 → ℝ → ℝ} {S : ℝ} {o : Option (Fin 2 × ℝ)}
    (ho : IsStage2Outcome1 ω σ S o) (l : Fin 2) (hl : CanAfford ω σ l S) : o ≠ none := by
  obtain ⟨_, h2, h3⟩ := ho
  by_cases ho' : CanAfford ω σ (other l) S
  · have hb : CanAfford ω σ 0 S ∧ CanAfford ω σ 1 S := by
      fin_cases l
      · exact ⟨hl, ho'⟩
      · exact ⟨ho', hl⟩
    obtain ⟨_, _, i, w, h, _⟩ := h3 hb.1 hb.2
    rw [h]; simp
  · obtain ⟨w, h, _⟩ := h2 l hl ho'
    rw [h]; simp

end stage2

section eq1
variable (ω : Params) (hG : Good ω)
include hG

lemma witness {σ : Fin 2 → ℝ → ℝ} (hσ : IsOptPricing1 ω σ) (out : ℝ → Option (Fin 2 × ℝ))
    (hout : ∀ S, 0 ≤ S → IsStage2Outcome1 ω σ S (out S)) :
    0 ≤ SoptR (ω.v 0) (ω.v 1) ∧ out (SoptR (ω.v 0) (ω.v 1)) ≠ none ∧
      payoff1 ω σ (SoptR (ω.v 0) (ω.v 1)) (out (SoptR (ω.v 0) (ω.v 1))) =
        LvR (ω.v 0) (ω.v 1) - ω.K := by
  have hv0 := v_pos ω hG 0
  have hv1 := v_pos ω hG 1
  have hS := SoptR_nonneg _ _ hv0 hv1
  refine ⟨hS, ?_⟩
  unfold SoptR LvR at *
  by_cases hv : ω.v 1 ≤ ω.v 0
  · simp only [hv, if_true] at hS ⊢
    by_cases hm : 3 * ω.v 0 / 16 ≤ ω.v 1 / 4
    · simp only [hm, if_true] at hS ⊢
      obtain ⟨w, hw, hp⟩ := att0 ω hG hσ (hout 0 le_rfl)
      refine ⟨by rw [hw]; simp, ?_⟩
      rw [hp]; unfold MvR; simp only [hv, if_true]
      rw [max_eq_right hm, max_eq_right (by linarith)]
    · simp only [hm, if_false] at hS ⊢
      push Not at hm
      obtain ⟨w, hw, hp⟩ := attTop ω hG hσ 0 (by rw [other0]; linarith) (hout _ hS)
      refine ⟨by rw [hw]; simp, ?_⟩
      rw [hp, max_eq_left hm.le]
  · simp only [hv, if_false] at hS ⊢
    push Not at hv
    by_cases hm : 3 * ω.v 1 / 16 ≤ ω.v 0 / 4
    · simp only [hm, if_true] at hS ⊢
      obtain ⟨w, hw, hp⟩ := att0 ω hG hσ (hout 0 le_rfl)
      refine ⟨by rw [hw]; simp, ?_⟩
      rw [hp]; unfold MvR; simp only [show ¬ ω.v 1 ≤ ω.v 0 from not_le.mpr hv, if_false]
      rw [max_eq_left hm, max_eq_left (by linarith)]
    · simp only [hm, if_false] at hS ⊢
      push Not at hm
      obtain ⟨w, hw, hp⟩ := attTop ω hG hσ 1 (by rw [other1]; linarith) (hout _ hS)
      refine ⟨by rw [hw]; simp, ?_⟩
      rw [hp, max_eq_right hm.le]

lemma eq1_true (P : Play1) (h : IsEq1 true ω P) :
    P.value ω = LvR (ω.v 0) (ω.v 1) - ω.K ∧
      ∃ w, P.outcome P.fee = some (idxR (ω.v 0) (ω.v 1), w) := by
  obtain ⟨hσ, hout, hfee⟩ := h
  rw [if_pos rfl] at hfee
  obtain ⟨⟨⟨hf0, hfn⟩, hfmax⟩, _⟩ := hfee
  obtain ⟨⟨i, w⟩, hiw⟩ := Option.ne_none_iff_exists'.mp hfn
  have hc := char1 ω hG hσ hf0 (hout _ hf0) hiw
  obtain ⟨hw0, hwn, hwv⟩ := witness ω hG hσ P.outcome hout
  have := hfmax _ ⟨hw0, hwn⟩
  rw [hwv] at this
  have heq : P.value ω = LvR (ω.v 0) (ω.v 1) - ω.K := le_antisymm hc.1 this
  refine ⟨heq, w, ?_⟩
  rw [hiw, (hc.2 heq).1]

lemma eq1_false (P : Play1) (h : IsEq1 false ω P) :
    P.value ω = MvR (ω.v 0) (ω.v 1) - ω.K ∧
      ∃ w, P.outcome P.fee = some (idxR (ω.v 0) (ω.v 1), w) := by
  obtain ⟨hσ, hout, hfee⟩ := h
  rw [if_neg (by decide)] at hfee
  obtain ⟨w, hw, hp⟩ := att0 ω hG hσ (hout 0 le_rfl)
  unfold Play1.value
  rw [hfee]
  exact ⟨hp, w, hw⟩

lemma pstar_opt : IsOptPricing1 ω (pstar ω) := by
  intro i w hc
  have hq := hq_pos ω hG i
  have hw : 0 ≤ w := le_trans (hG i).1 hc
  refine ⟨pstar_mem ω i w hq hw, fun p hp => ?_⟩
  rw [gross1_pstar ω i w hq hw]
  have := gross1_le ω i w p hq hw hp.1 hp.2
  have : 0 ≤ (if w ≤ ω.q i then (p - (ω.q i + w) / 2) ^ 2 / ω.q i else 0) := by
    split_ifs <;> positivity
  linarith

lemma exists_eq1 (fees : Bool) : ∃ P, IsEq1 fees ω P := by
  have hσ := pstar_opt ω hG
  let out : ℝ → Option (Fin 2 × ℝ) := fun S =>
    if h : 0 ≤ S then Classical.choose (exists_outcome1 ω hG hσ h) else none
  have hout : ∀ S, 0 ≤ S → IsStage2Outcome1 ω (pstar ω) S (out S) := by
    intro S h
    simp only [out, dif_pos h]
    exact Classical.choose_spec (exists_outcome1 ω hG hσ h)
  cases fees
  · exact ⟨⟨pstar ω, out, 0⟩, hσ, hout, by rw [if_neg (by decide)]⟩
  · refine ⟨⟨pstar ω, out, SoptR (ω.v 0) (ω.v 1)⟩, hσ, hout, ?_⟩
    rw [if_pos rfl]
    obtain ⟨hw0, hwn, hwv⟩ := witness ω hG hσ out hout
    have bound : ∀ S', Play1.Offers ⟨pstar ω, out, SoptR (ω.v 0) (ω.v 1)⟩ S' →
        payoff1 ω (pstar ω) S' (out S') ≤ LvR (ω.v 0) (ω.v 1) - ω.K ∧
        (payoff1 ω (pstar ω) S' (out S') = LvR (ω.v 0) (ω.v 1) - ω.K →
          SoptR (ω.v 0) (ω.v 1) ≤ S') := by
      rintro S' ⟨h0, hn⟩
      obtain ⟨⟨i, w⟩, hiw⟩ := Option.ne_none_iff_exists'.mp hn
      have hc := char1 ω hG hσ h0 (hout _ h0) hiw
      exact ⟨hc.1, fun he => (hc.2 he).2⟩
    refine ⟨⟨⟨hw0, hwn⟩, fun S' hS' => ?_⟩, fun S hS => ?_⟩
    · show payoff1 ω (pstar ω) S' (out S') ≤ payoff1 ω (pstar ω) _ (out _)
      rw [hwv]; exact (bound S' hS').1
    · obtain ⟨hoff, hmax⟩ := hS
      have h1 := hmax _ ⟨hw0, hwn⟩
      have h2 := bound S hoff
      change payoff1 ω (pstar ω) _ (out _) ≤ payoff1 ω (pstar ω) S (out S) at h1
      rw [hwv] at h1
      exact h2.2 (le_antisymm h2.1 h1)

end eq1

/-! ## Two-product stage 3 -/

noncomputable def D0 (q0 q1 p0 p1 : ℝ) : ℝ := max 0 (1 - max (p0 / q0) ((p0 - p1) / (q0 - q1)))
noncomputable def D1 (q0 q1 p0 p1 : ℝ) : ℝ := max 0 (min 1 ((p0 - p1) / (q0 - q1)) - p1 / q1)
noncomputable def Z0r (q0 q1 x y : ℝ) : ℝ :=
  max 0 (min ((q0 - x) / (2 * q0)) ((q0 - q1 - x + y) / (2 * (q0 - q1))))
noncomputable def Z1r (q0 q1 x y : ℝ) : ℝ :=
  max 0 (min ((q1 - y) / (2 * q1)) ((q1 * x - q0 * y) / (2 * q1 * (q0 - q1))))
def Phir (q0 q1 x y z0 z1 : ℝ) : ℝ :=
  (q0 - x) * z0 + (q1 - y) * z1 - q0 * z0 ^ 2 - 2 * q1 * z0 * z1 - q1 * z1 ^ 2

lemma dem0_eq (ω : Params) (hq1 : 0 < ω.q 1) (hd : ω.q 1 < ω.q 0) (p : Fin 2 → ℝ)
    (hp : ∀ l, 0 ≤ p l) : demand ω Finset.univ p 0 = D0 (ω.q 0) (ω.q 1) (p 0) (p 1) := by
  have hq0 : 0 < ω.q 0 := by linarith
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  unfold demand D0
  rw [if_pos (Finset.mem_univ _)]
  have hset : {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ * ω.q 0 - p 0 ∧
      ∀ j ∈ (Finset.univ : Finset (Fin 2)), θ * ω.q j - p j ≤ θ * ω.q 0 - p 0}
      = Set.Icc (max (p 0 / ω.q 0) ((p 0 - p 1) / (ω.q 0 - ω.q 1))) 1 := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Finset.mem_univ, true_implies, Fin.forall_fin_two,
      le_refl, true_and, and_true, max_le_iff, div_le_iff₀ hq0, div_le_iff₀ hd']
    have := hp 0
    constructor
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩
      refine ⟨⟨?_, h1⟩, by linarith, by linarith⟩
      by_contra h; push Not at h; nlinarith
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

lemma dem1_eq (ω : Params) (hq1 : 0 < ω.q 1) (hd : ω.q 1 < ω.q 0) (p : Fin 2 → ℝ)
    (hp : ∀ l, 0 ≤ p l) : demand ω Finset.univ p 1 = D1 (ω.q 0) (ω.q 1) (p 0) (p 1) := by
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  unfold demand D1
  rw [if_pos (Finset.mem_univ _)]
  have hset : {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ * ω.q 1 - p 1 ∧
      ∀ j ∈ (Finset.univ : Finset (Fin 2)), θ * ω.q j - p j ≤ θ * ω.q 1 - p 1}
      = Set.Icc (p 1 / ω.q 1) (min 1 ((p 0 - p 1) / (ω.q 0 - ω.q 1))) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Finset.mem_univ, true_implies, Fin.forall_fin_two,
      le_refl, and_true, le_min_iff, div_le_iff₀ hq1, le_div_iff₀ hd']
    have := hp 1
    constructor
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨by linarith, h1, by linarith⟩
    · rintro ⟨h2, h1, h3⟩
      refine ⟨⟨?_, h1⟩, by linarith, by linarith⟩
      by_contra h; push Not at h; nlinarith
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

lemma gross2_eq (ω : Params) (w p : Fin 2 → ℝ) :
    grossProfit ω Finset.univ w p =
      (p 0 - w 0) * demand ω Finset.univ p 0 + (p 1 - w 1) * demand ω Finset.univ p 1 := by
  unfold grossProfit; rw [Fin.sum_univ_two]

section real2
variable {q0 q1 : ℝ} (hq1 : 0 < q1) (hd : q1 < q0)
include hq1 hd

lemma R_le_Phi (x y p0 p1 : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) :
    (p0 - x) * D0 q0 q1 p0 p1 + (p1 - y) * D1 q0 q1 p0 p1 ≤
      Phir q0 q1 x y (D0 q0 q1 p0 p1) (D1 q0 q1 p0 p1) := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  set u := p0 / q0 with hu
  set s := (p0 - p1) / (q0 - q1) with hs
  set t := p1 / q1 with ht
  have eu : u * q0 = p0 := by rw [hu]; field_simp
  have es : s * (q0 - q1) = p0 - p1 := by rw [hs]; field_simp
  have et : t * q1 = p1 := by rw [ht]; field_simp
  have hsu : (s - u) * ((q0 - q1) * q0) = q1 * p0 - q0 * p1 := by
    linear_combination q0 * es - (q0 - q1) * eu
  have hst : (s - t) * ((q0 - q1) * q1) = q1 * p0 - q0 * p1 := by
    linear_combination q1 * es - (q0 - q1) * et
  have hdq0 : 0 < (q0 - q1) * q0 := by positivity
  have hdq1 : 0 < (q0 - q1) * q1 := by positivity
  unfold D0 D1 Phir
  rw [← hu, ← hs, ← ht]
  clear_value u s t
  set z0 := max 0 (1 - max u s) with hz0
  set z1 := max 0 (min 1 s - t) with hz1
  suffices h : 0 ≤ z0 * (q0 - q0 * z0 - q1 * z1 - p0) + z1 * (q1 - q1 * z0 - q1 * z1 - p1) by
    nlinarith
  rcases le_or_gt (min 1 s - t) 0 with h1 | h1
  · have : z1 = 0 := max_eq_left h1
    rw [this, hz0]
    rcases le_or_gt (1 - max u s) 0 with h0 | h0
    · rw [max_eq_left h0]; simp
    · rw [max_eq_right h0.le]
      have : q0 * u ≤ q0 * max u s := mul_le_mul_of_nonneg_left (le_max_left _ _) hq0.le
      have : 0 ≤ q0 - q0 * (1 - max u s) - q1 * 0 - p0 := by nlinarith
      exact add_nonneg (mul_nonneg h0.le this) (by simp)
  · have hst' : t < s := lt_of_lt_of_le (by linarith) (min_le_right 1 s)
    have hsu' : u < s := by
      have : 0 < (s - t) * ((q0 - q1) * q1) := mul_pos (by linarith) hdq1
      have : 0 < (s - u) * ((q0 - q1) * q0) := by linarith
      by_contra hh; push Not at hh
      nlinarith
    rw [max_eq_right hsu'.le] at hz0
    have hz1' : z1 = min 1 s - t := max_eq_right h1.le
    rcases le_total s 1 with hs1 | hs1
    · rw [min_eq_right hs1] at hz1'
      have hz0' : z0 = 1 - s := by rw [hz0]; exact max_eq_right (by linarith)
      have e1 : q0 - q0 * z0 - q1 * z1 - p0 = 0 := by
        rw [hz0', hz1']; linear_combination es + et
      have e2 : q1 - q1 * z0 - q1 * z1 - p1 = 0 := by
        rw [hz0', hz1']; linear_combination et
      rw [e1, e2]; simp
    · rw [min_eq_left hs1] at hz1'
      have hz0' : z0 = 0 := by rw [hz0]; exact max_eq_left (by linarith)
      have e2 : q1 - q1 * z0 - q1 * z1 - p1 = 0 := by
        rw [hz0', hz1']; linear_combination et
      rw [e2, hz0']; simp

lemma Z_int {x y : ℝ} (h1 : q0 * y ≤ q1 * x) (h2 : x ≤ q0 - q1 + y) :
    Z0r q0 q1 x y = (q0 - q1 - x + y) / (2 * (q0 - q1)) ∧
      Z1r q0 q1 x y = (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have e1 : (q0 - x) / (2 * q0) - (q0 - q1 - x + y) / (2 * (q0 - q1)) =
      (q1 * x - q0 * y) / (2 * q0 * (q0 - q1)) := by field_simp; ring
  have e2 : (q1 - y) / (2 * q1) - (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) =
      (q0 - q1 + y - x) / (2 * (q0 - q1)) := by field_simp; ring
  have n1 : 0 ≤ (q1 * x - q0 * y) / (2 * q0 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  have n2 : 0 ≤ (q0 - q1 + y - x) / (2 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  have n3 : 0 ≤ (q0 - q1 - x + y) / (2 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  have n4 : 0 ≤ (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  unfold Z0r Z1r
  rw [min_eq_right (by linarith), min_eq_right (by linarith), max_eq_right n3, max_eq_right n4]
  exact ⟨rfl, rfl⟩

lemma Z_A {x y : ℝ} (h1 : q1 * x ≤ q0 * y) :
    Z0r q0 q1 x y = max 0 ((q0 - x) / (2 * q0)) ∧ Z1r q0 q1 x y = 0 := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have e1 : (q0 - q1 - x + y) / (2 * (q0 - q1)) - (q0 - x) / (2 * q0) =
      (q0 * y - q1 * x) / (2 * q0 * (q0 - q1)) := by field_simp; ring
  have n1 : 0 ≤ (q0 * y - q1 * x) / (2 * q0 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  have n2 : (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  unfold Z0r Z1r
  rw [min_eq_left (by linarith)]
  exact ⟨rfl, max_eq_left (le_trans (min_le_right _ _) n2)⟩

lemma Z_B {x y : ℝ} (h1 : q0 - q1 + y ≤ x) :
    Z0r q0 q1 x y = 0 ∧ Z1r q0 q1 x y = max 0 ((q1 - y) / (2 * q1)) := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have e2 : (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) - (q1 - y) / (2 * q1) =
      (x - (q0 - q1 + y)) / (2 * (q0 - q1)) := by field_simp; ring
  have n1 : 0 ≤ (x - (q0 - q1 + y)) / (2 * (q0 - q1)) := div_nonneg (by linarith) (by positivity)
  have n2 : (q0 - q1 - x + y) / (2 * (q0 - q1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  unfold Z0r Z1r
  rw [min_eq_left (a := (q1 - y) / (2 * q1)) (by linarith)]
  exact ⟨max_eq_left (le_trans (min_le_right _ _) n2), rfl⟩

lemma kkt (x y : ℝ) :
    (q0 - x - 2 * q0 * Z0r q0 q1 x y - 2 * q1 * Z1r q0 q1 x y) ≤ 0 ∧
    (q1 - y - 2 * q1 * Z0r q0 q1 x y - 2 * q1 * Z1r q0 q1 x y) ≤ 0 ∧
    (q0 - x - 2 * q0 * Z0r q0 q1 x y - 2 * q1 * Z1r q0 q1 x y) * Z0r q0 q1 x y = 0 ∧
    (q1 - y - 2 * q1 * Z0r q0 q1 x y - 2 * q1 * Z1r q0 q1 x y) * Z1r q0 q1 x y = 0 := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  rcases lt_or_ge (q1 * x) (q0 * y) with hA | hA
  · obtain ⟨e0, e1⟩ := Z_A hq1 hd hA.le
    rw [e0, e1]
    rcases le_total x q0 with hx | hx
    · rw [max_eq_right (div_nonneg (by linarith) (by positivity))]
      have : q0 - x - 2 * q0 * ((q0 - x) / (2 * q0)) - 2 * q1 * 0 = 0 := by field_simp; ring
      rw [this]
      have : q1 - y - 2 * q1 * ((q0 - x) / (2 * q0)) - 2 * q1 * 0 = (q1 * x - q0 * y) / q0 := by
        field_simp; ring
      rw [this]
      exact ⟨le_rfl, div_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le, by simp, by simp⟩
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
      have hy : q1 ≤ y := by nlinarith
      refine ⟨by linarith, by linarith, by simp, by simp⟩
  · rcases le_total x (q0 - q1 + y) with hB | hB
    · obtain ⟨e0, e1⟩ := Z_int hq1 hd hA hB
      rw [e0, e1]
      have g0 : q0 - x - 2 * q0 * ((q0 - q1 - x + y) / (2 * (q0 - q1))) -
          2 * q1 * ((q1 * x - q0 * y) / (2 * q1 * (q0 - q1))) = 0 := by field_simp; ring
      have g1 : q1 - y - 2 * q1 * ((q0 - q1 - x + y) / (2 * (q0 - q1))) -
          2 * q1 * ((q1 * x - q0 * y) / (2 * q1 * (q0 - q1))) = 0 := by field_simp; ring
      rw [g0, g1]; simp
    · obtain ⟨e0, e1⟩ := Z_B hq1 hd hB
      rw [e0, e1]
      rcases le_total y q1 with hy | hy
      · rw [max_eq_right (div_nonneg (by linarith) (by positivity))]
        have : q1 - y - 2 * q1 * 0 - 2 * q1 * ((q1 - y) / (2 * q1)) = 0 := by field_simp; ring
        rw [this]
        have : q0 - x - 2 * q0 * 0 - 2 * q1 * ((q1 - y) / (2 * q1)) = q0 - q1 + y - x := by
          field_simp; ring
        rw [this]
        exact ⟨by linarith, le_rfl, by simp, by simp⟩
      · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
        refine ⟨by linarith, by linarith, by simp, by simp⟩

lemma Phi_gap (x y z0 z1 : ℝ) (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1) :
    Phir q0 q1 x y z0 z1 + ((q0 - q1) * (z0 - Z0r q0 q1 x y) ^ 2 +
      q1 * (z0 - Z0r q0 q1 x y + z1 - Z1r q0 q1 x y) ^ 2) ≤
      Phir q0 q1 x y (Z0r q0 q1 x y) (Z1r q0 q1 x y) := by
  obtain ⟨g0, g1, k0, k1⟩ := kkt hq1 hd x y
  set A := Z0r q0 q1 x y
  set B := Z1r q0 q1 x y
  unfold Phir
  have : (q0 - x - 2 * q0 * A - 2 * q1 * B) * z0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg g0 hz0
  have : (q1 - y - 2 * q1 * A - 2 * q1 * B) * z1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg g1 hz1
  nlinarith

end real2

section real2b
variable {q0 q1 : ℝ} (hq1 : 0 < q1) (hd : q1 < q0)
include hq1 hd

lemma attain (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    D0 q0 q1 ((q0 + min x q0) / 2) ((q1 + min y q1) / 2) = Z0r q0 q1 x y ∧
    D1 q0 q1 ((q0 + min x q0) / 2) ((q1 + min y q1) / 2) = Z1r q0 q1 x y := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  unfold D0 D1
  rcases lt_or_ge (q1 * x) (q0 * y) with hA | hA
  · obtain ⟨e0, e1⟩ := Z_A hq1 hd hA.le
    rw [e0, e1]
    rcases le_total x q0 with hx0 | hx0
    · rw [min_eq_left hx0]
      have hu : (q0 + x) / 2 / q0 = (q0 + x) / (2 * q0) := by field_simp
      have hsu : ((q0 + x) / 2 - (q1 + min y q1) / 2) / (q0 - q1) ≤ (q0 + x) / 2 / q0 := by
        rw [div_le_div_iff₀ hd' hq0]
        rcases le_total y q1 with hy1 | hy1
        · rw [min_eq_left hy1]; nlinarith
        · rw [min_eq_right hy1]; nlinarith
      have hst : ((q0 + x) / 2 - (q1 + min y q1) / 2) / (q0 - q1) ≤ (q1 + min y q1) / 2 / q1 := by
        rw [div_le_div_iff₀ hd' hq1]
        rcases le_total y q1 with hy1 | hy1
        · rw [min_eq_left hy1]; nlinarith
        · rw [min_eq_right hy1]; nlinarith
      rw [max_eq_left hsu, hu]
      refine ⟨?_, ?_⟩
      · congr 1; field_simp; ring
      · apply max_eq_left
        linarith [min_le_right 1 (((q0 + x) / 2 - (q1 + min y q1) / 2) / (q0 - q1))]
    · rw [min_eq_right hx0]
      have hy1 : q1 ≤ y := by nlinarith
      rw [min_eq_right hy1]
      have h1 : (q0 + q0) / 2 / q0 = 1 := by field_simp; ring
      have h2 : (q1 + q1) / 2 / q1 = 1 := by field_simp; ring
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
        apply max_eq_left; linarith [le_max_left 1 (((q0 + q0) / 2 - (q1 + q1) / 2) / (q0 - q1))]
      · apply max_eq_left
        linarith [min_le_left 1 (((q0 + q0) / 2 - (q1 + q1) / 2) / (q0 - q1))]
  · rcases le_or_gt x (q0 - q1 + y) with hB | hB
    · obtain ⟨e0, e1⟩ := Z_int hq1 hd hA hB
      rw [e0, e1]
      have hy1 : y ≤ q1 := by nlinarith
      have hx0 : x ≤ q0 := by linarith
      rw [min_eq_left hx0, min_eq_left hy1]
      have hs : ((q0 + x) / 2 - (q1 + y) / 2) / (q0 - q1) = (q0 - q1 + x - y) / (2 * (q0 - q1)) := by
        field_simp; ring
      have hu : (q0 + x) / 2 / q0 = (q0 + x) / (2 * q0) := by field_simp
      have ht : (q1 + y) / 2 / q1 = (q1 + y) / (2 * q1) := by field_simp
      rw [hs, hu, ht]
      have hus : (q0 + x) / (2 * q0) ≤ (q0 - q1 + x - y) / (2 * (q0 - q1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have hs1 : (q0 - q1 + x - y) / (2 * (q0 - q1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      rw [max_eq_right hus, min_eq_right hs1]
      have a1 : 1 - (q0 - q1 + x - y) / (2 * (q0 - q1)) = (q0 - q1 - x + y) / (2 * (q0 - q1)) := by
        field_simp; ring
      have a2 : (q0 - q1 + x - y) / (2 * (q0 - q1)) - (q1 + y) / (2 * q1) =
          (q1 * x - q0 * y) / (2 * q1 * (q0 - q1)) := by field_simp; ring
      rw [a1, a2]
      exact ⟨max_eq_right (div_nonneg (by linarith) (by positivity)),
        max_eq_right (div_nonneg (by linarith) (by positivity))⟩
    · obtain ⟨e0, e1⟩ := Z_B hq1 hd hB.le
      rw [e0, e1]
      rcases le_total y q1 with hy1 | hy1
      · rw [min_eq_left hy1]
        have hs1 : 1 ≤ ((q0 + min x q0) / 2 - (q1 + y) / 2) / (q0 - q1) := by
          rw [one_le_div hd']
          rcases le_total x q0 with hx0 | hx0
          · rw [min_eq_left hx0]; linarith
          · rw [min_eq_right hx0]; linarith
        rw [min_eq_left hs1]
        have ht : 1 - (q1 + y) / 2 / q1 = (q1 - y) / (2 * q1) := by field_simp; ring
        rw [ht]
        have hm := le_max_right ((q0 + min x q0) / 2 / q0)
          (((q0 + min x q0) / 2 - (q1 + y) / 2) / (q0 - q1))
        exact ⟨max_eq_left (by linarith), rfl⟩
      · have hx0 : q0 ≤ x := by linarith
        rw [min_eq_right hy1, min_eq_right hx0]
        have h1 : (q0 + q0) / 2 / q0 = 1 := by field_simp; ring
        have h2 : (q1 + q1) / 2 / q1 = 1 := by field_simp; ring
        rw [h1, h2, max_eq_left (b := (q1 - y) / (2 * q1))
          (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
        refine ⟨?_, ?_⟩
        · apply max_eq_left; linarith [le_max_left 1 (((q0 + q0) / 2 - (q1 + q1) / 2) / (q0 - q1))]
        · apply max_eq_left
          linarith [min_le_left 1 (((q0 + q0) / 2 - (q1 + q1) / 2) / (q0 - q1))]

lemma attain_val (x y : ℝ) :
    ((q0 + min x q0) / 2 - x) * Z0r q0 q1 x y + ((q1 + min y q1) / 2 - y) * Z1r q0 q1 x y =
      Phir q0 q1 x y (Z0r q0 q1 x y) (Z1r q0 q1 x y) := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  unfold Phir
  rcases lt_or_ge (q1 * x) (q0 * y) with hA | hA
  · obtain ⟨e0, e1⟩ := Z_A hq1 hd hA.le
    rw [e0, e1]
    rcases le_total x q0 with hx0 | hx0
    · rw [min_eq_left hx0, max_eq_right (div_nonneg (by linarith) (by positivity))]
      field_simp; ring
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]; ring
  · rcases le_or_gt x (q0 - q1 + y) with hB | hB
    · obtain ⟨e0, e1⟩ := Z_int hq1 hd hA hB
      rw [e0, e1]
      have hy1 : y ≤ q1 := by nlinarith
      have hx0 : x ≤ q0 := by linarith
      rw [min_eq_left hx0, min_eq_left hy1]
      field_simp; ring
    · obtain ⟨e0, e1⟩ := Z_B hq1 hd hB.le
      rw [e0, e1]
      rcases le_total y q1 with hy1 | hy1
      · rw [min_eq_left hy1, max_eq_right (div_nonneg (by linarith) (by positivity))]
        field_simp; ring
      · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]; ring

end real2b

section ne
variable {q0 q1 c0 c1 : ℝ} (hq1 : 0 < q1) (hd : q1 < q0)
include hq1 hd

omit hq1 hd in
lemma pi0_le (x y : ℝ) (hx : c0 ≤ x) :
    (x - c0) * Z0r q0 q1 x y ≤ max 0 ((x - c0) * (q0 - q1 - x + y) / (2 * (q0 - q1))) := by
  have h : Z0r q0 q1 x y ≤ max 0 ((q0 - q1 - x + y) / (2 * (q0 - q1))) :=
    max_le_max le_rfl (min_le_right _ _)
  calc (x - c0) * Z0r q0 q1 x y ≤ (x - c0) * max 0 ((q0 - q1 - x + y) / (2 * (q0 - q1))) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ = _ := by rw [mul_max_of_nonneg _ _ (by linarith), mul_zero, mul_div_assoc]

omit hq1 hd in
lemma pi1_le (x y : ℝ) (hy : c1 ≤ y) :
    (y - c1) * Z1r q0 q1 x y ≤ max 0 ((y - c1) * (q1 * x - q0 * y) / (2 * q1 * (q0 - q1))) := by
  have h : Z1r q0 q1 x y ≤ max 0 ((q1 * x - q0 * y) / (2 * q1 * (q0 - q1))) :=
    max_le_max le_rfl (min_le_right _ _)
  calc (y - c1) * Z1r q0 q1 x y ≤ (y - c1) * max 0 ((q1 * x - q0 * y) / (2 * q1 * (q0 - q1))) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ = _ := by rw [mul_max_of_nonneg _ _ (by linarith), mul_zero, mul_div_assoc]

lemma Z0_pos (x y : ℝ) (h1 : x < q0) (h2 : x < q0 - q1 + y) : 0 < Z0r q0 q1 x y := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  unfold Z0r
  exact lt_max_of_lt_right (lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity)))

lemma Z1_pos (x y : ℝ) (h1 : y < q1) (h2 : q0 * y < q1 * x) : 0 < Z1r q0 q1 x y := by
  have hd' : 0 < q0 - q1 := by linarith
  unfold Z1r
  exact lt_max_of_lt_right (lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity)))

variable (hc0 : 0 ≤ c0) (hc0q : c0 < q0) (hc1 : 0 ≤ c1) (hc1q : c1 < q1)
  (he0 : 0 < (2 * q0 - q1) * (q0 - c0) - q0 * (q1 - c1))
  (he1 : 0 < (2 * q0 - q1) * (q1 - c1) - q1 * (q0 - c0))
include hc0 hc0q hc1 hc1q he0 he1

lemma NE_exists {xs ys : ℝ} (hxs : 2 * xs = q0 - q1 + ys + c0)
    (hys : 2 * q0 * ys = q1 * xs + q0 * c1) (p0 : c0 < xs) (p1 : c1 < ys) :
    (∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x ys ≤ (xs - c0) * Z0r q0 q1 xs ys) ∧
    (∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 xs y ≤ (ys - c1) * Z1r q0 q1 xs ys) ∧
    (∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x ys = (xs - c0) * Z0r q0 q1 xs ys → xs ≤ x) ∧
    (∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 xs y = (ys - c1) * Z1r q0 q1 xs ys → ys ≤ y) := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have hi1 : q0 * ys ≤ q1 * xs := by nlinarith
  have hi2 : xs ≤ q0 - q1 + ys := by linarith
  obtain ⟨e0, e1⟩ := Z_int hq1 hd hi1 hi2
  have v0 : (xs - c0) * Z0r q0 q1 xs ys = (xs - c0) * (q0 - q1 - xs + ys) / (2 * (q0 - q1)) := by
    rw [e0, mul_div_assoc]
  have v1 : (ys - c1) * Z1r q0 q1 xs ys =
      (ys - c1) * (q1 * xs - q0 * ys) / (2 * q1 * (q0 - q1)) := by rw [e1, mul_div_assoc]
  have f0 : ∀ x, (x - c0) * (q0 - q1 - x + ys) =
      (xs - c0) * (q0 - q1 - xs + ys) - (x - xs) ^ 2 := by
    intro x; linear_combination (xs - x) * hxs
  have f1 : ∀ y, (y - c1) * (q1 * xs - q0 * y) =
      (ys - c1) * (q1 * xs - q0 * ys) - q0 * (y - ys) ^ 2 := by
    intro y; linear_combination (ys - y) * hys
  have P0 : 0 < (xs - c0) * (q0 - q1 - xs + ys) / (2 * (q0 - q1)) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have P1 : 0 < (ys - c1) * (q1 * xs - q0 * ys) / (2 * q1 * (q0 - q1)) :=
    div_pos (mul_pos (by linarith) (by nlinarith)) (by positivity)
  have B0 : ∀ x, (x - c0) * (q0 - q1 - x + ys) / (2 * (q0 - q1)) =
      (xs - c0) * (q0 - q1 - xs + ys) / (2 * (q0 - q1)) - (x - xs) ^ 2 / (2 * (q0 - q1)) := by
    intro x; rw [f0 x, sub_div]
  have B1 : ∀ y, (y - c1) * (q1 * xs - q0 * y) / (2 * q1 * (q0 - q1)) =
      (ys - c1) * (q1 * xs - q0 * ys) / (2 * q1 * (q0 - q1)) -
        q0 * (y - ys) ^ 2 / (2 * q1 * (q0 - q1)) := by
    intro y; rw [f1 y, sub_div]
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun x hx he => ?_, fun y hy he => ?_⟩
  · have := pi0_le x ys hx (c0 := c0) (q0 := q0) (q1 := q1)
    rw [v0]; refine le_trans this (max_le P0.le ?_)
    rw [B0 x]; have : 0 ≤ (x - xs) ^ 2 / (2 * (q0 - q1)) := by positivity
    linarith
  · have := pi1_le xs y hy (c1 := c1) (q0 := q0) (q1 := q1)
    rw [v1]; refine le_trans this (max_le P1.le ?_)
    rw [B1 y]; have : 0 ≤ q0 * (y - ys) ^ 2 / (2 * q1 * (q0 - q1)) := by positivity
    linarith
  · have := pi0_le x ys hx (c0 := c0) (q0 := q0) (q1 := q1)
    rw [he, v0] at this
    rcases le_max_iff.mp this with h | h
    · linarith
    · rw [B0 x] at h
      have : (x - xs) ^ 2 / (2 * (q0 - q1)) ≤ 0 := by linarith
      have : (x - xs) ^ 2 ≤ 0 := by
        by_contra hc; have := div_pos (not_le.mp hc) (by positivity : (0:ℝ) < 2 * (q0 - q1))
        linarith
      exact le_of_eq (sq_le_zero_eq this).symm
  · have := pi1_le xs y hy (c1 := c1) (q0 := q0) (q1 := q1)
    rw [he, v1] at this
    rcases le_max_iff.mp this with h | h
    · linarith
    · rw [B1 y] at h
      have : q0 * (y - ys) ^ 2 / (2 * q1 * (q0 - q1)) ≤ 0 := by linarith
      have : q0 * (y - ys) ^ 2 ≤ 0 := by
        by_contra hc
        have := div_pos (not_le.mp hc) (by positivity : (0:ℝ) < 2 * q1 * (q0 - q1))
        linarith
      have h3 : (y - ys) ^ 2 ≤ 0 := by
        by_contra hc; have := mul_pos hq0 (not_le.mp hc); linarith
      exact le_of_eq (sq_le_zero_eq h3).symm

end ne

section ne2
variable {q0 q1 c0 c1 : ℝ} (hq1 : 0 < q1) (hd : q1 < q0)
  (hc0 : 0 ≤ c0) (hc0q : c0 < q0) (hc1 : 0 ≤ c1) (hc1q : c1 < q1)
  (he0 : 0 < (2 * q0 - q1) * (q0 - c0) - q0 * (q1 - c1))
  (he1 : 0 < (2 * q0 - q1) * (q1 - c1) - q1 * (q0 - c0))
  {X Y : ℝ} (hX : c0 ≤ X) (hY : c1 ≤ Y)
  (h0 : ∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x Y ≤ (X - c0) * Z0r q0 q1 X Y)
  (h1 : ∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 X y ≤ (Y - c1) * Z1r q0 q1 X Y)
  (s0 : ∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x Y = (X - c0) * Z0r q0 q1 X Y → X ≤ x)
  (s1 : ∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 X y = (Y - c1) * Z1r q0 q1 X Y → Y ≤ y)
include hq1 hd hc0 hc0q hc1 hc1q he0 he1 hX hY h0 h1 s0 s1

omit s0 in
lemma caseA (hA : q1 * X ≤ q0 * Y) : False := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have h2d : 0 < 2 * (q0 - q1) := by positivity
  have z1 : Z1r q0 q1 X Y = 0 := (Z_A hq1 hd hA).2
  have hXc : q1 * X ≤ q0 * c1 := by
    by_contra hc; push Not at hc
    set y' := (c1 + min q1 (q1 * X / q0)) / 2 with hy'
    have hm1 : c1 < min q1 (q1 * X / q0) :=
      lt_min hc1q (by rw [lt_div_iff₀ hq0]; linarith)
    have hy'c : c1 < y' := by linarith
    have hy'q : y' < q1 := by linarith [min_le_left q1 (q1 * X / q0)]
    have hy'X : q0 * y' < q1 * X := by
      have : y' < q1 * X / q0 := by linarith [min_le_right q1 (q1 * X / q0)]
      rw [lt_div_iff₀ hq0] at this; linarith
    have hp := Z1_pos hq1 hd X y' hy'q hy'X
    have := h1 y' hy'c.le
    rw [z1, mul_zero] at this
    have : 0 < (y' - c1) * Z1r q0 q1 X y' := mul_pos (by linarith) hp
    linarith
  have hYc : Y = c1 := by
    have := s1 c1 le_rfl (by
      rw [(Z_A hq1 hd (by linarith : q1 * X ≤ q0 * c1)).2, z1]; simp)
    linarith
  subst hYc
  have hcc : c0 * q1 ≤ q0 * Y := by nlinarith
  have hx'1 : q1 * ((q0 - q1 + Y + c0) / 2) - q0 * Y =
      ((2 * q0 - q1) * (q1 - Y) - q1 * (q0 - c0)) / 2 := by ring
  have hx'2 : (q0 - q1 + Y + c0) / 2 < q0 - q1 + Y := by
    have : (c0 - Y) * q1 < (q0 - q1) * q1 := by nlinarith
    have : c0 - Y < q0 - q1 := lt_of_mul_lt_mul_right this hq1.le
    linarith
  have hXx' : X < (q0 - q1 + Y + c0) / 2 := by
    have : q1 * X < q1 * ((q0 - q1 + Y + c0) / 2) := by linarith
    exact lt_of_mul_lt_mul_left this hq1.le
  obtain ⟨e0, _⟩ := Z_int hq1 hd (by linarith : q0 * Y ≤ q1 * ((q0 - q1 + Y + c0) / 2)) hx'2.le
  have hb := pi0_le X Y hX (c0 := c0) (q0 := q0) (q1 := q1)
  have hdev := h0 ((q0 - q1 + Y + c0) / 2) (by linarith)
  rw [e0, ← mul_div_assoc] at hdev
  have hpos : 0 < ((q0 - q1 + Y + c0) / 2 - c0) * (q0 - q1 - (q0 - q1 + Y + c0) / 2 + Y) /
      (2 * (q0 - q1)) := div_pos (mul_pos (by linarith) (by linarith)) h2d
  rcases le_max_iff.mp (le_trans hdev hb) with h | h
  · linarith
  · rw [div_le_div_iff_of_pos_right h2d] at h
    have id : (X - c0) * (q0 - q1 - X + Y) = ((q0 - q1 + Y + c0) / 2 - c0) *
        (q0 - q1 - (q0 - q1 + Y + c0) / 2 + Y) - (X - (q0 - q1 + Y + c0) / 2) ^ 2 := by ring
    have : 0 < (X - (q0 - q1 + Y + c0) / 2) ^ 2 := by
      have h' : X - (q0 - q1 + Y + c0) / 2 < 0 := by linarith
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (ne_of_lt h')))
    linarith

omit s1 in
lemma caseB (hA' : q0 * Y < q1 * X) (hB : q0 - q1 + Y < X) : False := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have z0 : Z0r q0 q1 X Y = 0 := (Z_B hq1 hd hB.le).1
  have hYc0 : q0 - q1 + Y ≤ c0 := by
    by_contra hc; push Not at hc
    set x' := (c0 + min q0 (q0 - q1 + Y)) / 2 with hx'
    have hm : c0 < min q0 (q0 - q1 + Y) := lt_min hc0q hc
    have hp := Z0_pos hq1 hd x' Y (by linarith [min_le_left q0 (q0 - q1 + Y)])
      (by linarith [min_le_right q0 (q0 - q1 + Y)])
    have := h0 x' (by linarith)
    rw [z0, mul_zero] at this
    have : 0 < (x' - c0) * Z0r q0 q1 x' Y := mul_pos (by linarith) hp
    linarith
  have hXc : X = c0 := by
    have := s0 c0 le_rfl (by rw [z0]; simp)
    linarith
  subst hXc
  have hYy' : Y < X - (q0 - q1) := by linarith
  have hy'q : X - (q0 - q1) < q1 := by linarith
  obtain ⟨_, f1⟩ := Z_B hq1 hd (by linarith : q0 - q1 + (X - (q0 - q1)) ≤ X)
  obtain ⟨_, g1⟩ := Z_B hq1 hd hYc0
  rw [max_eq_right (div_nonneg (by linarith) (by positivity))] at f1 g1
  have := h1 (X - (q0 - q1)) (by linarith)
  rw [f1, g1, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right (by positivity)] at this
  have h2y : 2 * (X - (q0 - q1)) < q1 + c1 := by nlinarith
  have id : (X - (q0 - q1) - c1) * (q1 - (X - (q0 - q1))) - (Y - c1) * (q1 - Y) =
      (X - (q0 - q1) - Y) * (q1 + c1 - (X - (q0 - q1)) - Y) := by ring
  have : 0 < (X - (q0 - q1) - Y) * (q1 + c1 - (X - (q0 - q1)) - Y) :=
    mul_pos (by linarith) (by linarith)
  linarith

omit s0 s1 h1 in
lemma caseC1 (hA' : q0 * Y < q1 * X) (hC : X ≤ q0 - q1 + Y) : 2 * X = q0 - q1 + Y + c0 := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have h2d : 0 < 2 * (q0 - q1) := by positivity
  obtain ⟨e0, _⟩ := Z_int hq1 hd hA'.le hC
  have hcY : c0 ≤ q0 - q1 + Y := by linarith
  set x2 := (q0 - q1 + Y + c0) / 2 with hx2
  have id : ∀ x, (x - c0) * (q0 - q1 - x + Y) =
      (x2 - c0) * (q0 - q1 - x2 + Y) - (x - x2) ^ 2 := by intro x; rw [hx2]; ring
  by_cases hx2i : q0 * Y ≤ q1 * x2
  · obtain ⟨f0, _⟩ := Z_int hq1 hd hx2i (by rw [hx2]; linarith)
    have := h0 x2 (by rw [hx2]; linarith)
    rw [e0, f0, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right h2d, id X] at this
    have : (X - x2) ^ 2 ≤ 0 := by linarith
    have : X = x2 := sq_le_zero_eq this
    rw [this, hx2]; ring
  · exfalso
    push Not at hx2i
    have ex' : q1 * (q0 * Y / q1) = q0 * Y := by field_simp
    have hx'X : q0 * Y / q1 < X := by
      have : q1 * (q0 * Y / q1) < q1 * X := by linarith
      exact lt_of_mul_lt_mul_left this hq1.le
    have hx2x' : x2 < q0 * Y / q1 := by
      have : q1 * x2 < q1 * (q0 * Y / q1) := by linarith
      exact lt_of_mul_lt_mul_left this hq1.le
    obtain ⟨f0, _⟩ := Z_int hq1 hd ex'.symm.le (by linarith)
    have := h0 (q0 * Y / q1) (by rw [hx2] at hx2x'; linarith)
    rw [e0, f0, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right h2d,
      id X, id (q0 * Y / q1)] at this
    have : 0 < (X - q0 * Y / q1) * (X + q0 * Y / q1 - 2 * x2) :=
      mul_pos (by linarith) (by linarith)
    have e : (X - x2) ^ 2 - (q0 * Y / q1 - x2) ^ 2 =
      (X - q0 * Y / q1) * (X + q0 * Y / q1 - 2 * x2) := by ring
    linarith

omit s0 s1 h0 in
lemma caseC2 (hA' : q0 * Y < q1 * X) (hC : X ≤ q0 - q1 + Y)
    (st1 : 2 * X = q0 - q1 + Y + c0) : 2 * q0 * Y = q1 * X + q0 * c1 := by
  have hq0 : 0 < q0 := by linarith
  have hd' : 0 < q0 - q1 := by linarith
  have h2d : 0 < 2 * q1 * (q0 - q1) := by positivity
  obtain ⟨_, e1⟩ := Z_int hq1 hd hA'.le hC
  set y2 := (q1 * X + q0 * c1) / (2 * q0) with hy2
  have ey2 : 2 * q0 * y2 = q1 * X + q0 * c1 := by rw [hy2]; field_simp
  clear_value y2
  have hy2c : c1 < y2 := by nlinarith
  have hy2X : q0 * y2 ≤ q1 * X := by nlinarith
  have id : ∀ y, (y - c1) * (q1 * X - q0 * y) =
      (y2 - c1) * (q1 * X - q0 * y2) - q0 * (y - y2) ^ 2 := by
    intro y; linear_combination (y2 - y) * ey2
  by_cases hy2i : X ≤ q0 - q1 + y2
  · obtain ⟨_, f1⟩ := Z_int hq1 hd hy2X hy2i
    have := h1 y2 hy2c.le
    rw [e1, f1, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right h2d, id Y] at this
    have : q0 * (Y - y2) ^ 2 ≤ 0 := by linarith
    have : (Y - y2) ^ 2 ≤ 0 := by
      by_contra hc; have := mul_pos hq0 (not_le.mp hc); linarith
    have : Y = y2 := sq_le_zero_eq this
    rw [this, ey2]
  · exfalso
    push Not at hy2i
    have hy'Y : X - (q0 - q1) ≤ Y := by linarith
    rcases lt_or_eq_of_le hy'Y with hlt | heq
    · have hq : q0 * (X - (q0 - q1)) ≤ q1 * X := by
        have := mul_lt_mul_of_pos_left hlt hq0; linarith
      obtain ⟨_, f1⟩ := Z_int hq1 hd hq (by linarith)
      have := h1 (X - (q0 - q1)) (by linarith)
      rw [e1, f1, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right h2d,
        id Y, id (X - (q0 - q1))] at this
      have : 0 < q0 * ((Y - (X - (q0 - q1))) * (Y + (X - (q0 - q1)) - 2 * y2)) :=
        mul_pos hq0 (mul_pos (by linarith) (by linarith))
      have e : q0 * (Y - y2) ^ 2 - q0 * (X - (q0 - q1) - y2) ^ 2 =
          q0 * ((Y - (X - (q0 - q1))) * (Y + (X - (q0 - q1)) - 2 * y2)) := by ring
      linarith
    · have hXc0 : X = c0 := by linarith
      rw [hXc0] at hy2i ey2
      nlinarith

omit hX hY h0 h1 s0 s1 in
lemma NE_unique {xs ys : ℝ} (hxs : 2 * xs = q0 - q1 + ys + c0)
    (hys : 2 * q0 * ys = q1 * xs + q0 * c1) {X Y : ℝ} (hX : c0 ≤ X) (hY : c1 ≤ Y)
    (h0 : ∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x Y ≤ (X - c0) * Z0r q0 q1 X Y)
    (h1 : ∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 X y ≤ (Y - c1) * Z1r q0 q1 X Y)
    (s0 : ∀ x, c0 ≤ x → (x - c0) * Z0r q0 q1 x Y = (X - c0) * Z0r q0 q1 X Y → X ≤ x)
    (s1 : ∀ y, c1 ≤ y → (y - c1) * Z1r q0 q1 X y = (Y - c1) * Z1r q0 q1 X Y → Y ≤ y) :
    X = xs ∧ Y = ys := by
  rcases le_or_gt (q1 * X) (q0 * Y) with hA | hA'
  · exact (caseA hq1 hd hc0 hc0q hc1 hc1q he0 he1 hX hY h0 h1 s1 hA).elim
  · rcases le_or_gt X (q0 - q1 + Y) with hC | hB
    · have st1 := caseC1 hq1 hd hc0 hc0q hc1 hc1q he0 he1 hX hY h0 hA' hC
      have st2 := caseC2 hq1 hd hc0 hc0q hc1 hc1q he0 he1 hX hY h1 hA' hC st1
      have hD : 0 < 4 * q0 - q1 := by linarith
      have k1 : (4 * q0 - q1) * (X - xs) = 0 := by linear_combination 2 * q0 * st1 + st2 - 2 * q0 * hxs - hys
      have hXs : X = xs := by
        rcases mul_eq_zero.mp k1 with h | h
        · linarith
        · linarith
      exact ⟨hXs, by rw [hXs] at st1; linarith⟩
    · exact (caseB hq1 hd hc0 hc0q hc1 hc1q he0 he1 hX hY h0 h1 s0 hA' hB).elim

end ne2

noncomputable def pst2 (ω : Params) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun l => (ω.q l + min (w l) (ω.q l)) / 2

noncomputable def ysw (ω : Params) : ℝ :=
  (ω.q 1 * (ω.q 0 - ω.q 1) + ω.q 1 * ω.c 0 + 2 * ω.q 0 * ω.c 1) / (4 * ω.q 0 - ω.q 1)
noncomputable def xsw (ω : Params) : ℝ := (ω.q 0 - ω.q 1 + ysw ω + ω.c 0) / 2

/-- The facts about `Ω` used below. -/
structure OF (ω : Params) : Prop where
  hq1 : 0 < ω.q 1
  hd : ω.q 1 < ω.q 0
  hc0 : 0 ≤ ω.c 0
  hc0q : ω.c 0 < ω.q 0
  hc1 : 0 ≤ ω.c 1
  hc1q : ω.c 1 < ω.q 1
  he0 : 0 < (2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) - ω.q 0 * (ω.q 1 - ω.c 1)
  he1 : 0 < (2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0)

lemma omega_facts {ω : Params} (hω : ω ∈ Omega) : OF ω := by
  obtain ⟨_, _, hc0q, hc0, hc1q, hc1, hl, hu⟩ := hω
  have hq1 : 0 < ω.q 1 := by linarith
  have ha1 : 0 < ω.q 1 - ω.c 1 := by linarith
  have ha0 : 0 < ω.q 0 - ω.c 0 := by linarith
  rw [div_lt_div_iff₀ ha1 hq1] at hu
  have h2 : 0 < 2 * ω.q 0 - ω.q 1 := by nlinarith
  rw [div_lt_div_iff₀ h2 ha1] at hl
  have he0 : 0 < (2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) - ω.q 0 * (ω.q 1 - ω.c 1) := by linarith
  have he1 : 0 < (2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0) := by linarith
  have hd : ω.q 1 < ω.q 0 := by nlinarith
  exact ⟨hq1, hd, hc0, hc0q, hc1, hc1q, he0, he1⟩

lemma OF.good {ω : Params} (h : OF ω) : Good ω := by
  intro l; fin_cases l
  · exact ⟨h.hc0, h.hc0q⟩
  · exact ⟨h.hc1, h.hc1q⟩

section two
variable {ω : Params} (hO : OF ω)
include hO

lemma ws_facts : 2 * xsw ω = ω.q 0 - ω.q 1 + ysw ω + ω.c 0 ∧
    2 * ω.q 0 * ysw ω = ω.q 1 * xsw ω + ω.q 0 * ω.c 1 ∧
    xsw ω - ω.c 0 = ((2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) - ω.q 0 * (ω.q 1 - ω.c 1)) /
      (4 * ω.q 0 - ω.q 1) ∧
    ysw ω - ω.c 1 = ((2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0)) /
      (4 * ω.q 0 - ω.q 1) := by
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith [hO.hq1, hO.hd]
  have hY : ysw ω * (4 * ω.q 0 - ω.q 1) =
      ω.q 1 * (ω.q 0 - ω.q 1) + ω.q 1 * ω.c 0 + 2 * ω.q 0 * ω.c 1 := by
    unfold ysw; rw [div_mul_cancel₀ _ hD.ne']
  unfold xsw
  refine ⟨by ring, by linear_combination hY / 2, ?_, ?_⟩
  · rw [eq_div_iff hD.ne']; linear_combination hY / 2
  · rw [eq_div_iff hD.ne']; linear_combination hY

lemma ws_pos : ω.c 0 < xsw ω ∧ ω.c 1 < ysw ω := by
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith [hO.hq1, hO.hd]
  obtain ⟨_, _, e0, e1⟩ := ws_facts hO
  have := div_pos hO.he0 hD
  have := div_pos hO.he1 hD
  constructor <;> linarith

lemma opt2 (w : Fin 2 → ℝ) (hw : ∀ l, 0 ≤ w l) :
    IsOptPrice2 ω w (pst2 ω w) ∧ grossProfit ω Finset.univ w (pst2 ω w) =
      Phir (ω.q 0) (ω.q 1) (w 0) (w 1) (Z0r (ω.q 0) (ω.q 1) (w 0) (w 1))
        (Z1r (ω.q 0) (ω.q 1) (w 0) (w 1)) := by
  have hq1 := hO.hq1
  have hd := hO.hd
  have hpn : ∀ l, 0 ≤ pst2 ω w l := by
    intro l; unfold pst2
    have : 0 < ω.q l := by fin_cases l <;> simp <;> linarith
    have := le_min (hw l) this.le
    linarith
  have hval : grossProfit ω Finset.univ w (pst2 ω w) =
      Phir (ω.q 0) (ω.q 1) (w 0) (w 1) (Z0r (ω.q 0) (ω.q 1) (w 0) (w 1))
        (Z1r (ω.q 0) (ω.q 1) (w 0) (w 1)) := by
    rw [gross2_eq, dem0_eq ω hq1 hd _ hpn, dem1_eq ω hq1 hd _ hpn]
    obtain ⟨a0, a1⟩ := attain hq1 hd (w 0) (w 1) (hw 0) (hw 1)
    simp only [pst2]
    rw [a0, a1]
    exact attain_val hq1 hd (w 0) (w 1)
  refine ⟨⟨hpn, fun p' hp' => ?_⟩, hval⟩
  rw [hval, gross2_eq, dem0_eq ω hq1 hd _ hp', dem1_eq ω hq1 hd _ hp']
  have h1 := R_le_Phi hq1 hd (w 0) (w 1) (p' 0) (p' 1) (hp' 0) (hp' 1)
  have h2 := Phi_gap hq1 hd (w 0) (w 1) (D0 (ω.q 0) (ω.q 1) (p' 0) (p' 1))
    (D1 (ω.q 0) (ω.q 1) (p' 0) (p' 1)) (by unfold D0; exact le_max_left _ _)
    (by unfold D1; exact le_max_left _ _)
  have : 0 ≤ (ω.q 0 - ω.q 1) * (D0 (ω.q 0) (ω.q 1) (p' 0) (p' 1) -
      Z0r (ω.q 0) (ω.q 1) (w 0) (w 1)) ^ 2 + ω.q 1 * (D0 (ω.q 0) (ω.q 1) (p' 0) (p' 1) -
      Z0r (ω.q 0) (ω.q 1) (w 0) (w 1) + D1 (ω.q 0) (ω.q 1) (p' 0) (p' 1) -
      Z1r (ω.q 0) (ω.q 1) (w 0) (w 1)) ^ 2 := by
    have : 0 < ω.q 0 - ω.q 1 := by linarith
    positivity
  linarith

lemma opt2_demand {w p : Fin 2 → ℝ} (hw : ∀ l, 0 ≤ w l) (hp : IsOptPrice2 ω w p) :
    demand ω Finset.univ p 0 = Z0r (ω.q 0) (ω.q 1) (w 0) (w 1) ∧
    demand ω Finset.univ p 1 = Z1r (ω.q 0) (ω.q 1) (w 0) (w 1) ∧
    grossProfit ω Finset.univ w p =
      Phir (ω.q 0) (ω.q 1) (w 0) (w 1) (Z0r (ω.q 0) (ω.q 1) (w 0) (w 1))
        (Z1r (ω.q 0) (ω.q 1) (w 0) (w 1)) := by
  have hq1 := hO.hq1
  have hd := hO.hd
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  obtain ⟨hpn, hmax⟩ := hp
  obtain ⟨hopt, hval⟩ := opt2 hO w hw
  have hge := hmax _ hopt.1
  rw [hval] at hge
  rw [gross2_eq, dem0_eq ω hq1 hd _ hpn, dem1_eq ω hq1 hd _ hpn] at hge ⊢
  have h1 := R_le_Phi hq1 hd (w 0) (w 1) (p 0) (p 1) (hpn 0) (hpn 1)
  have h2 := Phi_gap hq1 hd (w 0) (w 1) (D0 (ω.q 0) (ω.q 1) (p 0) (p 1))
    (D1 (ω.q 0) (ω.q 1) (p 0) (p 1)) (by unfold D0; exact le_max_left _ _)
    (by unfold D1; exact le_max_left _ _)
  set A := D0 (ω.q 0) (ω.q 1) (p 0) (p 1)
  set B := D1 (ω.q 0) (ω.q 1) (p 0) (p 1)
  set Z0 := Z0r (ω.q 0) (ω.q 1) (w 0) (w 1)
  set Z1 := Z1r (ω.q 0) (ω.q 1) (w 0) (w 1)
  have hs1 : 0 ≤ (ω.q 0 - ω.q 1) * (A - Z0) ^ 2 := by positivity
  have hs2 : 0 ≤ ω.q 1 * (A - Z0 + B - Z1) ^ 2 := by positivity
  have k1 : (ω.q 0 - ω.q 1) * (A - Z0) ^ 2 = 0 := by linarith
  have k2 : ω.q 1 * (A - Z0 + B - Z1) ^ 2 = 0 := by linarith
  have eA : A = Z0 := by
    rcases mul_eq_zero.mp k1 with h | h
    · linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
  have eB : A - Z0 + B - Z1 = 0 := by
    rcases mul_eq_zero.mp k2 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  refine ⟨eA, by linarith, ?_⟩
  linarith

lemma payoffs {σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hσ : IsOptPricing2 ω σ) (S : ℝ) {x y : ℝ}
    (hx : ω.c 0 ≤ x) (hy : ω.c 1 ≤ y) :
    wholesalePayoff1 ω σ S x y = (x - ω.c 0) * Z0r (ω.q 0) (ω.q 1) x y - S ∧
    wholesalePayoff2 ω σ S y x = (y - ω.c 1) * Z1r (ω.q 0) (ω.q 1) x y - S := by
  have hw : ∀ l, ω.c l ≤ (![x, y] : Fin 2 → ℝ) l := by
    intro l; fin_cases l <;> simpa
  have hw0 : ∀ l, 0 ≤ (![x, y] : Fin 2 → ℝ) l := by
    intro l; fin_cases l
    · simp; linarith [hO.hc0]
    · simp; linarith [hO.hc1]
  obtain ⟨d0, d1, _⟩ := opt2_demand hO hw0 (hσ _ hw)
  unfold wholesalePayoff1 wholesalePayoff2 mfrGross2 mfrGross
  rw [d0, d1]
  simp

lemma NE_holds {σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hσ : IsOptPricing2 ω σ) (S : ℝ) :
    IsSelectedNE2 ω σ S ![xsw ω, ysw ω] := by
  obtain ⟨f1, f2, _, _⟩ := ws_facts hO
  obtain ⟨p0, p1⟩ := ws_pos hO
  obtain ⟨n0, n1, n2, n3⟩ := NE_exists hO.hq1 hO.hd hO.hc0 hO.hc0q hO.hc1 hO.hc1q hO.he0 hO.he1 f1 f2 p0 p1
  have P := fun x y (hx : ω.c 0 ≤ x) (hy : ω.c 1 ≤ y) => payoffs hO hσ S hx hy
  unfold IsSelectedNE2 CrossLicensing.ExPost.IsNE
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ici]
  refine ⟨⟨p0.le, p1.le, fun x hx => ?_, fun y hy => ?_⟩,
    fun x hx he => ?_, fun y hy he => ?_⟩
  · rw [(P x _ hx p1.le).1, (P _ _ p0.le p1.le).1]; linarith [n0 x hx]
  · rw [(P _ y p0.le hy).2, (P _ _ p0.le p1.le).2]; linarith [n1 y hy]
  · rw [(P x _ hx p1.le).1, (P _ _ p0.le p1.le).1] at he
    exact n2 x hx (by linarith)
  · rw [(P _ y p0.le hy).2, (P _ _ p0.le p1.le).2] at he
    exact n3 y hy (by linarith)

lemma NE_eq {σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hσ : IsOptPricing2 ω σ) (S : ℝ) {w : Fin 2 → ℝ}
    (h : IsSelectedNE2 ω σ S w) : w = ![xsw ω, ysw ω] := by
  obtain ⟨f1, f2, _, _⟩ := ws_facts hO
  obtain ⟨⟨m0, m1, b0, b1⟩, s0, s1⟩ := h
  simp only [Set.mem_Ici] at m0 m1
  have P := fun x y (hx : ω.c 0 ≤ x) (hy : ω.c 1 ≤ y) => payoffs hO hσ S hx hy
  obtain ⟨e0, e1⟩ := NE_unique hO.hq1 hO.hd hO.hc0 hO.hc0q hO.hc1 hO.hc1q hO.he0 hO.he1 f1 f2
    m0 m1
    (fun x hx => by have := b0 x hx; rw [(P x _ hx m1).1, (P _ _ m0 m1).1] at this; linarith)
    (fun y hy => by have := b1 y hy; rw [(P _ y m0 hy).2, (P _ _ m0 m1).2] at this; linarith)
    (fun x hx he => s0 x hx (by rw [(P x _ hx m1).1, (P _ _ m0 m1).1]; linarith))
    (fun y hy he => s1 y hy (by rw [(P _ y m0 hy).2, (P _ _ m0 m1).2]; linarith))
  funext l; fin_cases l
  · simpa using e0
  · simpa using e1

end two

noncomputable def Vw (ω : Params) : ℝ :=
  Phir (ω.q 0) (ω.q 1) (xsw ω) (ysw ω) (Z0r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω))
    (Z1r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω))
noncomputable def pi0w (ω : Params) : ℝ := (xsw ω - ω.c 0) * Z0r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω)
noncomputable def pi1w (ω : Params) : ℝ := (ysw ω - ω.c 1) * Z1r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω)

section two2
variable {ω : Params} (hO : OF ω)
include hO

lemma ws_nonneg : ∀ l, 0 ≤ (![xsw ω, ysw ω] : Fin 2 → ℝ) l := by
  obtain ⟨p0, p1⟩ := ws_pos hO
  intro l; fin_cases l
  · simp; linarith [hO.hc0]
  · simp; linarith [hO.hc1]

lemma ws_ge : ∀ l, ω.c l ≤ (![xsw ω, ysw ω] : Fin 2 → ℝ) l := by
  obtain ⟨p0, p1⟩ := ws_pos hO
  intro l; fin_cases l
  · simp; linarith
  · simp; linarith

lemma mfr_at {σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hσ : IsOptPricing2 ω σ) :
    mfrGross2 ω σ ![xsw ω, ysw ω] 0 = pi0w ω ∧ mfrGross2 ω σ ![xsw ω, ysw ω] 1 = pi1w ω ∧
      grossProfit ω Finset.univ ![xsw ω, ysw ω] (σ ![xsw ω, ysw ω]) = Vw ω := by
  obtain ⟨d0, d1, g⟩ := opt2_demand hO (ws_nonneg hO) (hσ _ (ws_ge hO))
  unfold mfrGross2 mfrGross pi0w pi1w Vw
  rw [d0, d1, g]
  simp

lemma pi_vals : pi0w ω = ((2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) - ω.q 0 * (ω.q 1 - ω.c 1)) ^ 2 /
      (2 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1) ^ 2) ∧
    pi1w ω = ω.q 0 * ((2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0)) ^ 2 /
      (2 * ω.q 1 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1) ^ 2) ∧
    Z0r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω) =
      ((2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) - ω.q 0 * (ω.q 1 - ω.c 1)) /
        (2 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1)) ∧
    Z1r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω) =
      ω.q 0 * ((2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0)) /
        (2 * ω.q 1 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1)) := by
  have hq1 := hO.hq1
  have hd := hO.hd
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith
  obtain ⟨f1, f2, e0, e1⟩ := ws_facts hO
  obtain ⟨p0, p1⟩ := ws_pos hO
  obtain ⟨z0, z1⟩ := Z_int hq1 hd (by nlinarith : ω.q 0 * ysw ω ≤ ω.q 1 * xsw ω)
    (by linarith : xsw ω ≤ ω.q 0 - ω.q 1 + ysw ω)
  have hz0 : Z0r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω) = (xsw ω - ω.c 0) / (2 * (ω.q 0 - ω.q 1)) := by
    rw [z0]; congr 1; linarith
  have hz1 : Z1r (ω.q 0) (ω.q 1) (xsw ω) (ysw ω) =
      ω.q 0 * (ysw ω - ω.c 1) / (2 * ω.q 1 * (ω.q 0 - ω.q 1)) := by
    rw [z1]; congr 1; linarith
  unfold pi0w pi1w
  rw [hz0, hz1, e0, e1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

lemma pi_pos : 0 < pi0w ω ∧ 0 < pi1w ω := by
  obtain ⟨h0, h1, _, _⟩ := pi_vals hO
  have hq1 := hO.hq1
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith [hO.hd]
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith [hO.hd]
  have := hO.he0
  have := hO.he1
  rw [h0, h1]
  constructor
  · exact div_pos (pow_pos hO.he0 2) (by positivity)
  · exact div_pos (mul_pos (by linarith [hO.hd]) (pow_pos hO.he1 2)) (by positivity)

lemma v12_eq : ω.v12 = Vw ω := by
  have hq1 := hO.hq1
  have hd := hO.hd
  have hq0 : 0 < ω.q 0 := by linarith
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith
  have ha0 : 0 < ω.q 0 - ω.c 0 := by linarith [hO.hc0q]
  have ha1 : 0 < ω.q 1 - ω.c 1 := by linarith [hO.hc1q]
  obtain ⟨_, _, z0, z1⟩ := pi_vals hO
  obtain ⟨_, _, e0, e1⟩ := ws_facts hO
  have hsq : Real.sqrt (ω.q 0 * ω.v 0 * ω.q 1 * ω.v 1) = (ω.q 0 - ω.c 0) * (ω.q 1 - ω.c 1) := by
    have : ω.q 0 * ω.v 0 * ω.q 1 * ω.v 1 = ((ω.q 0 - ω.c 0) * (ω.q 1 - ω.c 1)) ^ 2 := by
      unfold Params.v; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  unfold Params.v12 Vw Phir
  rw [hsq, z0, z1]
  have ex : ω.q 0 - xsw ω = (ω.q 0 - ω.c 0) - (xsw ω - ω.c 0) := by ring
  have ey : ω.q 1 - ysw ω = (ω.q 1 - ω.c 1) - (ysw ω - ω.c 1) := by ring
  rw [ex, ey, e0, e1]
  unfold Params.v
  have hDne : 4 * ω.q 0 - ω.q 1 ≠ 0 := hD.ne'
  have hdne : ω.q 0 - ω.q 1 ≠ 0 := hd'.ne'
  have hDne' : ω.q 0 * 4 - ω.q 1 ≠ 0 := by rw [mul_comm]; exact hDne
  generalize ω.q 0 - ω.c 0 = a0
  generalize ω.q 1 - ω.c 1 = a1
  field_simp
  ring

lemma S2_eq : ω.S2 = min (pi0w ω) (pi1w ω) := by
  have hq1 := hO.hq1
  have hd := hO.hd
  have hq0 : 0 < ω.q 0 := by linarith
  have hd' : 0 < ω.q 0 - ω.q 1 := by linarith
  have hD : 0 < 4 * ω.q 0 - ω.q 1 := by linarith
  have ha0 : 0 < ω.q 0 - ω.c 0 := by linarith [hO.hc0q]
  have ha1 : 0 < ω.q 1 - ω.c 1 := by linarith [hO.hc1q]
  have he0 := hO.he0
  have he1 := hO.he1
  have hv0 : ω.v 0 * ω.q 0 = (ω.q 0 - ω.c 0) ^ 2 := by unfold Params.v; field_simp
  have hv1 : ω.v 1 * ω.q 1 = (ω.q 1 - ω.c 1) ^ 2 := by unfold Params.v; field_simp
  have vp0 : 0 < ω.v 0 := by unfold Params.v; positivity
  have vp1 : 0 < ω.v 1 := by unfold Params.v; positivity
  have h2 : 0 < 2 * ω.q 0 - ω.q 1 := by linarith
  have hcond : 1 - ω.vbar < ω.ratio ∧ ω.ratio < ω.vbar := by
    unfold Params.vbar Params.ratio
    have hp : 0 < ω.q 0 * ω.q 1 + (2 * ω.q 0 - ω.q 1) ^ 2 := by positivity
    have hvv : 0 < ω.v 0 + ω.v 1 := by linarith
    have k1 : (ω.q 1 - ω.c 1) * ω.q 0 < (2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0) := by linarith
    have k2 : (ω.q 0 - ω.c 0) * ω.q 1 < (2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) := by linarith
    have k1' : ((ω.q 1 - ω.c 1) * ω.q 0) ^ 2 < ((2 * ω.q 0 - ω.q 1) * (ω.q 0 - ω.c 0)) ^ 2 :=
      pow_lt_pow_left₀ k1 (by positivity) (by norm_num)
    have k2' : ((ω.q 0 - ω.c 0) * ω.q 1) ^ 2 < ((2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1)) ^ 2 :=
      pow_lt_pow_left₀ k2 (by positivity) (by norm_num)
    constructor
    · rw [one_sub_div hp.ne', div_lt_div_iff₀ hp hvv]
      have : ω.v 1 * (ω.q 0 * ω.q 1) * ω.q 0 < ω.v 0 * (2 * ω.q 0 - ω.q 1) ^ 2 * ω.q 0 := by
        have e1 : ω.v 1 * (ω.q 0 * ω.q 1) * ω.q 0 = (ω.q 1 - ω.c 1) ^ 2 * ω.q 0 ^ 2 := by
          rw [← hv1]; ring
        have e2 : ω.v 0 * (2 * ω.q 0 - ω.q 1) ^ 2 * ω.q 0 =
            (2 * ω.q 0 - ω.q 1) ^ 2 * (ω.q 0 - ω.c 0) ^ 2 := by rw [← hv0]; ring
        rw [e1, e2]; nlinarith
      have : ω.v 1 * (ω.q 0 * ω.q 1) < ω.v 0 * (2 * ω.q 0 - ω.q 1) ^ 2 :=
        lt_of_mul_lt_mul_right this hq0.le
      nlinarith
    · rw [div_lt_div_iff₀ hvv hp]
      have : ω.v 0 * (ω.q 0 * ω.q 1) * ω.q 1 < ω.v 1 * (2 * ω.q 0 - ω.q 1) ^ 2 * ω.q 1 := by
        have e1 : ω.v 0 * (ω.q 0 * ω.q 1) * ω.q 1 = (ω.q 0 - ω.c 0) ^ 2 * ω.q 1 ^ 2 := by
          rw [← hv0]; ring
        have e2 : ω.v 1 * (2 * ω.q 0 - ω.q 1) ^ 2 * ω.q 1 =
            (2 * ω.q 0 - ω.q 1) ^ 2 * (ω.q 1 - ω.c 1) ^ 2 := by rw [← hv1]; ring
        rw [e1, e2]; nlinarith
      have : ω.v 0 * (ω.q 0 * ω.q 1) < ω.v 1 * (2 * ω.q 0 - ω.q 1) ^ 2 :=
        lt_of_mul_lt_mul_right this hq1.le
      nlinarith
  unfold Params.S2
  rw [if_pos hcond]
  unfold Params.S2min
  obtain ⟨p0, p1, _, _⟩ := pi_vals hO
  rw [p0, p1]
  have s00 : Real.sqrt (ω.q 0 * ω.v 0) = ω.q 0 - ω.c 0 := by
    rw [mul_comm, hv0, Real.sqrt_sq ha0.le]
  have s11 : Real.sqrt (ω.q 1 * ω.v 1) = ω.q 1 - ω.c 1 := by
    rw [mul_comm, hv1, Real.sqrt_sq ha1.le]
  set s := Real.sqrt (ω.q 0 * ω.v 1) with hs
  set r := Real.sqrt (ω.q 1 * ω.v 0) with hr
  have hs2 : s ^ 2 = ω.q 0 * ω.v 1 := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = ω.q 1 * ω.v 0 := Real.sq_sqrt (by positivity)
  have hsr : s * r = (ω.q 0 - ω.c 0) * (ω.q 1 - ω.c 1) := by
    rw [hs, hr, ← Real.sqrt_mul (by positivity)]
    have : ω.q 0 * ω.v 1 * (ω.q 1 * ω.v 0) = ((ω.q 0 - ω.c 0) * (ω.q 1 - ω.c 1)) ^ 2 := by
      linear_combination (ω.v 1 * ω.q 1) * hv0 + (ω.q 0 - ω.c 0) ^ 2 * hv1
    rw [this, Real.sqrt_sq (by positivity)]
  rw [s00, s11]
  have hB : ((2 * ω.q 0 - ω.q 1) * s - ω.q 0 * r) ^ 2 = ω.q 0 *
      ((2 * ω.q 0 - ω.q 1) * (ω.q 1 - ω.c 1) - ω.q 1 * (ω.q 0 - ω.c 0)) ^ 2 / ω.q 1 := by
    rw [eq_div_iff hq1.ne']
    have e : ((2 * ω.q 0 - ω.q 1) * s - ω.q 0 * r) ^ 2 =
        (2 * ω.q 0 - ω.q 1) ^ 2 * s ^ 2 - 2 * (2 * ω.q 0 - ω.q 1) * ω.q 0 * (s * r) +
          ω.q 0 ^ 2 * r ^ 2 := by ring
    rw [e, hs2, hr2, hsr]
    linear_combination (ω.q 0 * (2 * ω.q 0 - ω.q 1) ^ 2) * hv1 + (ω.q 0 * ω.q 1 ^ 2) * hv0
  rw [hB, ← min_div_div_right (by positivity)]
  congr 1
  field_simp

end two2

section eq2
variable {ω : Params} (hO : OF ω)
include hO

lemma payoff2_eq {P : Play2} (hσ : IsOptPricing2 ω P.price) {S : ℝ}
    (hw : P.wholesale S = ![xsw ω, ysw ω]) : P.payoff ω S = Vw ω + 2 * S - 2 * ω.K := by
  obtain ⟨_, _, g⟩ := mfr_at hO hσ
  unfold Play2.payoff retailerProfit
  rw [hw, g]
  simp; ring

lemma eq2_true (P : Play2) (h : IsEq2 true ω P) :
    P.value ω = Vw ω + 2 * min (pi0w ω) (pi1w ω) - 2 * ω.K := by
  obtain ⟨hσ, hne, hfee⟩ := h
  rw [if_pos rfl] at hfee
  obtain ⟨⟨hf0, hfl⟩, hmax⟩ := hfee
  have hw : ∀ S, 0 ≤ S → P.wholesale S = ![xsw ω, ysw ω] := fun S hS => NE_eq hO hσ S (hne S hS)
  obtain ⟨m0, m1, _⟩ := mfr_at hO hσ
  obtain ⟨pp0, pp1⟩ := pi_pos hO
  have l0 := hfl 0
  have l1 := hfl 1
  rw [hw _ hf0, m0] at l0
  rw [hw _ hf0, m1] at l1
  have hmin0 : 0 ≤ min (pi0w ω) (pi1w ω) := le_min pp0.le pp1.le
  have hfeas : P.Feasible ω (min (pi0w ω) (pi1w ω)) := by
    refine ⟨hmin0, fun l => ?_⟩
    rw [hw _ hmin0]
    fin_cases l
    · simp only [Fin.zero_eta]; rw [m0]; linarith [min_le_left (pi0w ω) (pi1w ω)]
    · simp only [Fin.mk_one]; rw [m1]; linarith [min_le_right (pi0w ω) (pi1w ω)]
  have := hmax _ hfeas
  rw [payoff2_eq hO hσ (hw _ hmin0), payoff2_eq hO hσ (hw _ hf0)] at this
  have hfe : P.fee = min (pi0w ω) (pi1w ω) :=
    le_antisymm (le_min (by linarith) (by linarith)) (by linarith)
  unfold Play2.value
  rw [payoff2_eq hO hσ (hw _ hf0), hfe]

lemma eq2_false (P : Play2) (h : IsEq2 false ω P) : P.value ω = Vw ω - 2 * ω.K := by
  obtain ⟨hσ, hne, hfee⟩ := h
  rw [if_neg (by decide)] at hfee
  unfold Play2.value
  rw [payoff2_eq hO hσ (by rw [hfee]; exact NE_eq hO hσ 0 (hne 0 le_rfl)), hfee]
  ring

lemma exists_eq2 (fees : Bool) : ∃ P, IsEq2 fees ω P := by
  have hσ : IsOptPricing2 ω (pst2 ω) := by
    intro w hw
    have hw0 : ∀ l, 0 ≤ w l := by
      intro l; fin_cases l
      · simp; linarith [hw 0, hO.hc0]
      · simp; linarith [hw 1, hO.hc1]
    exact (opt2 hO w hw0).1
  obtain ⟨m0, m1, _⟩ := mfr_at hO hσ
  obtain ⟨pp0, pp1⟩ := pi_pos hO
  cases fees
  · exact ⟨⟨pst2 ω, fun _ => ![xsw ω, ysw ω], 0⟩, hσ, fun S _ => NE_holds hO hσ S,
      by rw [if_neg (by decide)]⟩
  · refine ⟨⟨pst2 ω, fun _ => ![xsw ω, ysw ω], min (pi0w ω) (pi1w ω)⟩, hσ,
      fun S _ => NE_holds hO hσ S, ?_⟩
    rw [if_pos rfl]
    have hmin0 : 0 ≤ min (pi0w ω) (pi1w ω) := le_min pp0.le pp1.le
    refine ⟨⟨hmin0, fun l => ?_⟩, fun S hS => ?_⟩
    · fin_cases l
      · simp only [Fin.zero_eta]; rw [m0]; linarith [min_le_left (pi0w ω) (pi1w ω)]
      · simp only [Fin.mk_one]; rw [m1]; linarith [min_le_right (pi0w ω) (pi1w ω)]
    · obtain ⟨hS0, hl⟩ := hS
      have l0 := hl 0
      have l1 := hl 1
      simp only [] at l0 l1
      rw [m0] at l0
      rw [m1] at l1
      rw [payoff2_eq hO hσ rfl, payoff2_eq hO hσ rfl]
      have : S ≤ min (pi0w ω) (pi1w ω) := le_min (by linarith) (by linarith)
      linarith

end eq2

/-! ## Region logic -/

section regions
variable (v0 v1 v12 S2 K : ℝ) (hv0 : 0 < v0) (hv1 : 0 < v1) (hS2 : 0 < S2)
include hv0 hv1 hS2

lemma reg_up
    (h : (v1 ≤ v0 ∧ v12 - max (v0 / 16) (v1 / 4) ≤ K ∧ K < v12 + 2 * S2 - max (3 * v0 / 16) (v1 / 4)) ∨
      (v0 < v1 ∧ v12 - max (v0 / 4) (v1 / 16) ≤ K ∧ K < v12 + 2 * S2 - max (v0 / 4) (3 * v1 / 16))) :
    ¬ (MvR v0 v1 - K < v12 - 2 * K) ∧ (LvR v0 v1 - K < v12 + 2 * S2 - 2 * K) := by
  unfold MvR LvR
  rcases h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
  · simp only [hv, if_true]; constructor <;> [intro h; skip] <;> linarith
  · simp only [show ¬ v1 ≤ v0 from not_le.mpr hv, if_false]
    constructor <;> [intro h; skip] <;> linarith

lemma reg_dn
    (h : (v1 ≤ v0 ∧ v12 + 2 * S2 - 3 * v0 / 16 ≤ K ∧ K < v12 - max (v0 / 16) (v1 / 4)) ∨
      (v0 < v1 ∧ v12 + 2 * S2 - 3 * v1 / 16 ≤ K ∧ K < v12 - max (v0 / 4) (v1 / 16))) :
    (MvR v0 v1 - K < v12 - 2 * K) ∧ ¬ (LvR v0 v1 - K < v12 + 2 * S2 - 2 * K) := by
  unfold MvR LvR
  rcases h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
  · simp only [hv, if_true]
    have := le_max_left (3 * v0 / 16) (v1 / 4)
    constructor <;> [skip; intro h] <;> linarith
  · simp only [show ¬ v1 ≤ v0 from not_le.mpr hv, if_false]
    have := le_max_right (v0 / 4) (3 * v1 / 16)
    constructor <;> [skip; intro h] <;> linarith

lemma reg_zero
    (hu : ¬ ((v1 ≤ v0 ∧ v12 - max (v0 / 16) (v1 / 4) ≤ K ∧
        K < v12 + 2 * S2 - max (3 * v0 / 16) (v1 / 4)) ∨
      (v0 < v1 ∧ v12 - max (v0 / 4) (v1 / 16) ≤ K ∧ K < v12 + 2 * S2 - max (v0 / 4) (3 * v1 / 16))))
    (hd : ¬ ((v1 ≤ v0 ∧ v12 + 2 * S2 - 3 * v0 / 16 ≤ K ∧ K < v12 - max (v0 / 16) (v1 / 4)) ∨
      (v0 < v1 ∧ v12 + 2 * S2 - 3 * v1 / 16 ≤ K ∧ K < v12 - max (v0 / 4) (v1 / 16)))) :
    (LvR v0 v1 - K < v12 + 2 * S2 - 2 * K ↔ MvR v0 v1 - K < v12 - 2 * K) := by
  unfold MvR LvR
  by_cases hv : v1 ≤ v0
  · simp only [hv, if_true]
    have hu' := fun a b => hu (Or.inl ⟨hv, a, b⟩)
    have hd' := fun a b => hd (Or.inl ⟨hv, a, b⟩)
    constructor
    · intro h
      by_contra hc; push Not at hc
      exact hu' (by linarith) (by linarith)
    · intro h
      by_contra hc; push Not at hc
      rcases le_total (3 * v0 / 16) (v1 / 4) with hm | hm
      · rw [max_eq_right hm] at hc
        rw [max_eq_right (by linarith : v0 / 16 ≤ v1 / 4)] at h
        linarith
      · rw [max_eq_left hm] at hc
        exact hd' (by linarith) (by linarith)
  · simp only [hv, if_false]
    push Not at hv
    have hu' := fun a b => hu (Or.inr ⟨hv, a, b⟩)
    have hd' := fun a b => hd (Or.inr ⟨hv, a, b⟩)
    constructor
    · intro h
      by_contra hc; push Not at hc
      exact hu' (by linarith) (by linarith)
    · intro h
      by_contra hc; push Not at hc
      rcases le_total (3 * v1 / 16) (v0 / 4) with hm | hm
      · rw [max_eq_left hm] at hc
        rw [max_eq_left (by linarith : v1 / 16 ≤ v0 / 4)] at h
        linarith
      · rw [max_eq_right hm] at hc
        exact hd' (by linarith) (by linarith)

end regions

theorem main (ω : Params) (hω : ω ∈ Omega) :
    (∃ A, IsEqAssortment true ω A) ∧ (∃ A, IsEqAssortment false ω A) ∧
    (ω ∈ PhiUp →
      (∀ A, IsEqAssortment false ω A → A = {0} ∨ A = {1}) ∧
      (∀ A, IsEqAssortment true ω A → A = Finset.univ)) ∧
    (ω ∈ PhiDown →
      (∀ A, IsEqAssortment false ω A → A = Finset.univ) ∧
      (∀ A, IsEqAssortment true ω A → A = {0} ∨ A = {1})) ∧
    (ω ∈ PhiZero →
      ∀ A B, IsEqAssortment true ω A → IsEqAssortment false ω B →
        A = B ∧ (A = {0} ∨ A = {1} ∨ A = Finset.univ)) := by
  have hO := omega_facts hω
  have hG := hO.good
  have hv0 := v_pos ω hG 0
  have hv1 := v_pos ω hG 1
  obtain ⟨pp0, pp1⟩ := pi_pos hO
  have hS2 : 0 < ω.S2 := by rw [S2_eq hO]; exact lt_min pp0 pp1
  have hT : ∀ A, IsEqAssortment true ω A → A =
      if LvR (ω.v 0) (ω.v 1) - ω.K < ω.v12 + 2 * ω.S2 - 2 * ω.K then Finset.univ
      else {idxR (ω.v 0) (ω.v 1)} := by
    rintro A ⟨P, ⟨h1, h2⟩, rfl⟩
    obtain ⟨e1, w, hw⟩ := eq1_true ω hG P.low h1
    have e2 := eq2_true hO P.high h2
    unfold Profile.assortment
    rw [e1, e2, hw, v12_eq hO, S2_eq hO]
  have hF : ∀ A, IsEqAssortment false ω A → A =
      if MvR (ω.v 0) (ω.v 1) - ω.K < ω.v12 - 2 * ω.K then Finset.univ
      else {idxR (ω.v 0) (ω.v 1)} := by
    rintro A ⟨P, ⟨h1, h2⟩, rfl⟩
    obtain ⟨e1, w, hw⟩ := eq1_false ω hG P.low h1
    have e2 := eq2_false hO P.high h2
    unfold Profile.assortment
    rw [e1, e2, hw, v12_eq hO]
  have hex : ∀ fees, ∃ A, IsEqAssortment fees ω A := by
    intro fees
    obtain ⟨P1, hP1⟩ := exists_eq1 ω hG fees
    obtain ⟨P2, hP2⟩ := exists_eq2 hO fees
    exact ⟨_, ⟨P1, P2⟩, ⟨hP1, hP2⟩, rfl⟩
  have hidx : ({idxR (ω.v 0) (ω.v 1)} : Finset (Fin 2)) = {0} ∨
      ({idxR (ω.v 0) (ω.v 1)} : Finset (Fin 2)) = {1} := by
    unfold idxR; split_ifs
    · left; rfl
    · right; rfl
  have up_iff : ω ∈ PhiUp ↔
      ((ω.v 1 ≤ ω.v 0 ∧ ω.v12 - max (ω.v 0 / 16) (ω.v 1 / 4) ≤ ω.K ∧
        ω.K < ω.v12 + 2 * ω.S2 - max (3 * ω.v 0 / 16) (ω.v 1 / 4)) ∨
      (ω.v 0 < ω.v 1 ∧ ω.v12 - max (ω.v 0 / 4) (ω.v 1 / 16) ≤ ω.K ∧
        ω.K < ω.v12 + 2 * ω.S2 - max (ω.v 0 / 4) (3 * ω.v 1 / 16))) := by
    unfold PhiUp
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
  have dn_iff : ω ∈ PhiDown ↔
      ((ω.v 1 ≤ ω.v 0 ∧ ω.v12 + 2 * ω.S2 - 3 * ω.v 0 / 16 ≤ ω.K ∧
        ω.K < ω.v12 - max (ω.v 0 / 16) (ω.v 1 / 4)) ∨
      (ω.v 0 < ω.v 1 ∧ ω.v12 + 2 * ω.S2 - 3 * ω.v 1 / 16 ≤ ω.K ∧
        ω.K < ω.v12 - max (ω.v 0 / 4) (ω.v 1 / 16))) := by
    unfold PhiDown
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
  refine ⟨hex true, hex false, fun hup => ?_, fun hdn => ?_, fun hz => ?_⟩
  · obtain ⟨r1, r2⟩ := reg_up _ _ _ _ _ hv0 hv1 hS2 (up_iff.mp hup)
    refine ⟨fun A hA => ?_, fun A hA => ?_⟩
    · rw [hF A hA, if_neg r1]; exact hidx
    · rw [hT A hA, if_pos r2]
  · obtain ⟨r1, r2⟩ := reg_dn _ _ _ _ _ hv0 hv1 hS2 (dn_iff.mp hdn)
    refine ⟨fun A hA => ?_, fun A hA => ?_⟩
    · rw [hF A hA, if_pos r1]
    · rw [hT A hA, if_neg r2]; exact hidx
  · have hnu : ω ∉ PhiUp := fun h => hz.2 (Or.inr h)
    have hnd : ω ∉ PhiDown := fun h => hz.2 (Or.inl h)
    rw [up_iff] at hnu
    rw [dn_iff] at hnd
    have r := reg_zero _ _ _ _ _ hv0 hv1 hS2 hnu hnd
    intro A B hA hB
    rw [hT A hA, hF B hB]
    by_cases h : LvR (ω.v 0) (ω.v 1) - ω.K < ω.v12 + 2 * ω.S2 - 2 * ω.K
    · rw [if_pos h, if_pos (r.mp h)]
      exact ⟨rfl, Or.inr (Or.inr rfl)⟩
    · rw [if_neg h, if_neg (fun h' => h (r.mpr h'))]
      refine ⟨rfl, ?_⟩
      rcases hidx with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')

end P5

theorem proposition_5 (ω : Params) (hω : ω ∈ Omega) :
    (∃ A, IsEqAssortment true ω A) ∧ (∃ A, IsEqAssortment false ω A) ∧
    (ω ∈ PhiUp →
      (∀ A, IsEqAssortment false ω A → A = {0} ∨ A = {1}) ∧
      (∀ A, IsEqAssortment true ω A → A = Finset.univ)) ∧
    (ω ∈ PhiDown →
      (∀ A, IsEqAssortment false ω A → A = Finset.univ) ∧
      (∀ A, IsEqAssortment true ω A → A = {0} ∨ A = {1})) ∧
    (ω ∈ PhiZero →
      ∀ A B, IsEqAssortment true ω A → IsEqAssortment false ω B →
        A = B ∧ (A = {0} ∨ A = {1} ∨ A = Finset.univ)) :=
  P5.main ω hω

end SlottingFees


-- Platform entry point: restates the target verbatim.
namespace SlottingFees

/-- **Proposition 5**, pp.20–21 (Alan, Kurtuluş, Nakkas, *Retail Category Management with
Slotting Fees*, MSOM 2024, doi:10.1287/msom.2022.0143), part (a) corrected: the impact of
slotting fees on the equilibrium product variety and assortment composition.

For every `ω ∈ Ω`, equilibria exist both in the main model and in the benchmark, and

* (a) on `Φ↑` every benchmark equilibrium assortment is `{1}` or `{2}`, and every main-model
  equilibrium assortment is `{1, 2}`;
* (b) on `Φ↓` every benchmark equilibrium assortment is `{1, 2}`, and every main-model
  equilibrium assortment is `{1}` or `{2}`;
* (c) on `Φ0 = Ω \ (Φ↓ ∪ Φ↑)` the two models have the same equilibrium assortment, which is
  `{1}`, `{2}` or `{1, 2}`.

**Formalization Note** `Φ↑` is corrected in its second set (see `PhiUp`); `Φ0` reads the printed
`Ω↓, Ω↑` as `Φ↓, Φ↑` (see `PhiZero`). Equilibrium assortments are those on the path of a
subgame-perfect equilibrium (`IsEqAssortment`). Products 1, 2 are `0`, `1`. -/
theorem _root_.solution (ω : Params) (hω : ω ∈ Omega) :
    (∃ A, IsEqAssortment true ω A) ∧ (∃ A, IsEqAssortment false ω A) ∧
    (ω ∈ PhiUp →
      (∀ A, IsEqAssortment false ω A → A = {0} ∨ A = {1}) ∧
      (∀ A, IsEqAssortment true ω A → A = Finset.univ)) ∧
    (ω ∈ PhiDown →
      (∀ A, IsEqAssortment false ω A → A = Finset.univ) ∧
      (∀ A, IsEqAssortment true ω A → A = {0} ∨ A = {1})) ∧
    (ω ∈ PhiZero →
      ∀ A B, IsEqAssortment true ω A → IsEqAssortment false ω B →
        A = B ∧ (A = {0} ∨ A = {1} ∨ A = Finset.univ)) := by
  apply @SlottingFees.proposition_5 <;> assumption

end SlottingFees
