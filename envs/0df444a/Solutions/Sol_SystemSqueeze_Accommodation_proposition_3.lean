-- Prove2me | solution 1 for SystemSqueeze.Accommodation.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:05:25.122263+00:00
-- url     : https://prove2.me/submissions/903423b6-d121-460c-b8d1-f8e5af4797ab

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

set_option autoImplicit false

open SystemSqueeze.Accommodation in
/-- First-order condition for a maximum of a concave quadratic. -/
lemma sq17_foc {f : ℝ → ℝ} {x V L k M : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hf : ∀ a, f a = V + ((a - x) * L - k * (a - x) ^ 2) / M) (hmax : ∀ a, f a ≤ V) :
    L = 0 := by
  have h := hmax (x + L / (2 * k))
  rw [hf] at h
  have h2 : ((x + L / (2 * k) - x) * L - k * (x + L / (2 * k) - x) ^ 2) ≤ 0 := by
    have h3 : ((x + L / (2 * k) - x) * L - k * (x + L / (2 * k) - x) ^ 2) / M ≤ 0 := by
      linarith
    have := (div_le_iff₀ hM).mp h3
    linarith
  have e : (x + L / (2 * k) - x) * L - k * (x + L / (2 * k) - x) ^ 2 = L ^ 2 / (4 * k) := by
    field_simp
    ring
  rw [e] at h2
  have h4 : L ^ 2 ≤ 0 := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * k)).mp h2
    linarith
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h4 (sq_nonneg L))

open SystemSqueeze.Accommodation in
lemma sq17_ne {UC x z : ℝ} (h : IsNoEntryEq UC ⟨x, z⟩) : x = UC / 3 ∧ z = UC / 3 := by
  have L1 := sq17_foc (f := fun a => profitA0 UC ⟨a, z⟩) (x := x)
    (V := profitA0 UC ⟨x, z⟩) (L := UC - 2 * x - z) (k := 1) (M := 1) one_pos one_pos
    (by intro a; simp only [profitA0, qC0]; ring) (fun a => h.1 a)
  have L2 := sq17_foc (f := fun b => profitB0 UC ⟨x, b⟩) (x := z)
    (V := profitB0 UC ⟨x, z⟩) (L := UC - x - 2 * z) (k := 1) (M := 1) one_pos one_pos
    (by intro a; simp only [profitB0, qC0]; ring) (fun b => h.2 b)
  constructor <;> linarith

open SystemSqueeze.Accommodation in
lemma sq17_acc {UC UI γ x y z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h : IsAccEq UC UI γ ⟨x, y, z⟩) :
    x = (2 * UC + γ * UI) / 6 ∧ y = UI / 2 ∧ z = (UC - γ * UI) / 3 := by
  have hD : 0 < (1 + γ) * (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  have L1 := sq17_foc (f := fun a => profitA1 UC UI γ ⟨a, y, z⟩) (x := x)
    (V := profitA1 UC UI γ ⟨x, y, z⟩) (L := UC - 2 * x - z - γ * UI + 2 * γ * y) (k := 1)
    (M := (1 + γ) * (1 - γ)) one_pos hD
    (by intro a; simp only [profitA1, qC1, qIA1]; ring) (fun a => h.1 a y)
  have L2 := sq17_foc (f := fun i => profitA1 UC UI γ ⟨x, i, z⟩) (x := y)
    (V := profitA1 UC UI γ ⟨x, y, z⟩) (L := UI - γ * UC + 2 * γ * x + γ * z - 2 * y) (k := 1)
    (M := (1 + γ) * (1 - γ)) one_pos hD
    (by intro a; simp only [profitA1, qC1, qIA1]; ring) (fun i => h.1 x i)
  have L3 := sq17_foc (f := fun b => profitB1 UC UI γ ⟨x, y, b⟩) (x := z)
    (V := profitB1 UC UI γ ⟨x, y, z⟩) (L := UC - x - 2 * z - γ * UI + γ * y) (k := 1)
    (M := (1 + γ) * (1 - γ)) one_pos hD
    (by intro a; simp only [profitB1, qC1]; ring) (fun b => h.2 b)
  have hy : (2 * y - UI) * (1 - γ ^ 2) = 0 := by linear_combination -L2 - γ * L1
  have hg : 1 - γ ^ 2 ≠ 0 := by nlinarith
  have hy' : y = UI / 2 := by
    rcases mul_eq_zero.mp hy with h1 | h1
    · linarith
    · exact absurd h1 hg
  subst hy'
  refine ⟨?_, rfl, ?_⟩ <;> linarith

open SystemSqueeze.Accommodation in
lemma sq17_esc {UC UI γ x y z w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h : IsEscEq UC UI γ ⟨x, y, z, w⟩) :
    x = ((2 - γ) * UC - γ * UI) / (3 * (2 - γ)) ∧ y = UI * (1 - γ) / (2 - γ) ∧
      z = ((2 - γ) * UC - γ * UI) / (3 * (2 - γ)) ∧ w = UI * (1 - γ) / (2 - γ) := by
  have hE : 0 < (1 + 2 * γ) * (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hk : 0 < 1 + γ := by linarith
  have A1 := sq17_foc (f := fun a => profitA2 UC UI γ ⟨a, y, z, w⟩) (x := x)
    (V := profitA2 UC UI γ ⟨x, y, z, w⟩)
    (L := (1 + γ) * (UC - 2 * x - z) - 2 * γ * UI + 2 * γ * y + γ * w) (k := 1 + γ)
    (M := (1 + 2 * γ) * (1 - γ)) hk hE
    (by intro a; simp only [profitA2, qC2, qIA2]; ring) (fun a => h.1 a y)
  have A2 := sq17_foc (f := fun i => profitA2 UC UI γ ⟨x, i, z, w⟩) (x := y)
    (V := profitA2 UC UI γ ⟨x, y, z, w⟩)
    (L := UI - γ * UC + 2 * γ * x + γ * z - 2 * (1 + γ) * y + γ * w) (k := 1 + γ)
    (M := (1 + 2 * γ) * (1 - γ)) hk hE
    (by intro a; simp only [profitA2, qC2, qIA2]; ring) (fun i => h.1 x i)
  have B1 := sq17_foc (f := fun b => profitB2 UC UI γ ⟨x, y, b, w⟩) (x := z)
    (V := profitB2 UC UI γ ⟨x, y, z, w⟩)
    (L := (1 + γ) * (UC - x - 2 * z) - 2 * γ * UI + γ * y + 2 * γ * w) (k := 1 + γ)
    (M := (1 + 2 * γ) * (1 - γ)) hk hE
    (by intro a; simp only [profitB2, qC2, qIB2]; ring) (fun b => h.2 b w)
  have B2 := sq17_foc (f := fun j => profitB2 UC UI γ ⟨x, y, z, j⟩) (x := w)
    (V := profitB2 UC UI γ ⟨x, y, z, w⟩)
    (L := UI - γ * UC + γ * x + 2 * γ * z + γ * y - 2 * (1 + γ) * w) (k := 1 + γ)
    (M := (1 + 2 * γ) * (1 - γ)) hk hE
    (by intro a; simp only [profitB2, qC2, qIB2]; ring) (fun j => h.2 z j)
  have hv : (y - w) * (2 + 5 * γ + 2 * γ ^ 2) = 0 := by
    linear_combination (-γ) * A1 + γ * B1 - (1 + γ) * A2 + (1 + γ) * B2
  have hvw : y = w := by
    rcases mul_eq_zero.mp hv with h1 | h1
    · linarith
    · nlinarith
  subst hvw
  have hu : (x - z) * (1 + γ) = 0 := by linear_combination -(A1 - B1)
  have hxz : x = z := by
    rcases mul_eq_zero.mp hu with h1 | h1
    · linarith
    · linarith
  subst hxz
  have h2g : (2 - γ) ≠ 0 := by intro h0; linarith
  have hx0 : (3 * (2 - γ) * x - ((2 - γ) * UC - γ * UI)) * (1 + 2 * γ) = 0 := by
    linear_combination -(2 + γ) * A1 - 3 * γ * A2
  have hx1 : 3 * (2 - γ) * x = (2 - γ) * UC - γ * UI := by
    rcases mul_eq_zero.mp hx0 with h1 | h1
    · linarith
    · linarith
  have hy0 : (2 + γ) * ((2 - γ) * y - UI * (1 - γ)) = 0 := by
    linear_combination -(2 - γ) * A2 + γ * hx1
  have hy1 : (2 - γ) * y = UI * (1 - γ) := by
    rcases mul_eq_zero.mp hy0 with h1 | h1
    · linarith
    · linarith
  have ex : x = ((2 - γ) * UC - γ * UI) / (3 * (2 - γ)) := by
    rw [eq_div_iff (by positivity)]; linarith
  have ey : y = UI * (1 - γ) / (2 - γ) := by
    rw [eq_div_iff h2g]; linarith
  exact ⟨ex, ey, ex, ey⟩

open SystemSqueeze.Accommodation in
lemma sq17_adm {UC UI γ : ℝ} (hUC : 0 < UC) (hUI : 0 < UI) (hγ : 0 < γ)
    (h : γ ≤ (Real.sqrt (UC ^ 2 + 3 * UI ^ 2) - UC) / UI) :
    γ ^ 2 * UI + 2 * γ * UC ≤ 3 * UI := by
  have h1 : γ * UI + UC ≤ Real.sqrt (UC ^ 2 + 3 * UI ^ 2) := by
    rw [le_div_iff₀ hUI] at h; linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [Real.sq_sqrt (by positivity)] at h2
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hUI (sub_pos.mpr hc)]

open SystemSqueeze.Accommodation in
theorem solution (UC UI : ℝ) (hUC : 0 < UC) (hUI : 0 < UI) :
    (∀ γ : ℝ, Standing UC UI γ →
      ∀ (n : NoEntryPrices) (a : AccPrices), IsNoEntryEq UC n → IsAccEq UC UI γ a →
        (UI < UC → dPiY UC UI γ n a < dPiX UC UI γ n a) ∧
        (UC < UI → dPiX UC UI γ n a < dPiY UC UI γ n a)) ∧
    (UI < UC → ∃ γhat : ℝ, γhat < gammaMax UC UI ∧
      ∀ γ : ℝ, γhat < γ → Standing UC UI γ →
        ∀ (n : NoEntryPrices) (a : AccPrices) (e : EscPrices),
          IsNoEntryEq UC n → IsAccEq UC UI γ a → IsEscEq UC UI γ e →
          ∃ K : ℝ, 0 ≤ K ∧ AccommodationOutcome UC UI γ n a e K ∧
            integratedProfitA UC UI γ a - K < 0) := by
  constructor
  · intro γ hS n a hn ha
    obtain ⟨_, _, hγ0, hγ1, hadm⟩ := hS
    rcases n with ⟨n1, n2⟩
    rcases a with ⟨a1, a2, a3⟩
    obtain ⟨rfl, rfl⟩ := sq17_ne hn
    obtain ⟨rfl, rfl, rfl⟩ := sq17_acc hγ0 hγ1 ha
    have h1g : 0 < 1 - γ := by linarith
    have hD : 0 < (1 + γ) * (1 - γ) := by positivity
    have key : dPiX UC UI γ ⟨UC / 3, UC / 3⟩ ⟨(2 * UC + γ * UI) / 6, UI / 2, (UC - γ * UI) / 3⟩
        - dPiY UC UI γ ⟨UC / 3, UC / 3⟩ ⟨(2 * UC + γ * UI) / 6, UI / 2, (UC - γ * UI) / 3⟩
        = γ * (UC - UI) * (3 * UI - γ * (2 * UC - UI)) / (18 * ((1 + γ) * (1 - γ))) := by
      simp only [dPiX, dPiY, qC0, qC1]
      field_simp
      ring
    constructor
    · intro hlt
      have hb := sq17_adm hUC hUI hγ0 (hadm.2 hlt)
      have hpos : 0 < 3 * UI - γ * (2 * UC - UI) := by nlinarith
      have : 0 < γ * (UC - UI) * (3 * UI - γ * (2 * UC - UI)) / (18 * ((1 + γ) * (1 - γ))) := by
        have : 0 < UC - UI := by linarith
        positivity
      linarith
    · intro hlt
      have hpos : 0 < 3 * UI - γ * (2 * UC - UI) := by nlinarith
      have : 0 < γ * (UI - UC) * (3 * UI - γ * (2 * UC - UI)) / (18 * ((1 + γ) * (1 - γ))) := by
        have : 0 < UI - UC := by linarith
        positivity
      have e2 : γ * (UC - UI) * (3 * UI - γ * (2 * UC - UI)) / (18 * ((1 + γ) * (1 - γ)))
          = -(γ * (UI - UC) * (3 * UI - γ * (2 * UC - UI)) / (18 * ((1 + γ) * (1 - γ)))) := by
        ring
      linarith
  · intro hlt
    have hs : 0 < 2 * UC ^ 2 - UI ^ 2 := by nlinarith
    refine ⟨UC * UI / (2 * UC ^ 2 - UI ^ 2), ?_, ?_⟩
    · -- the threshold lies strictly below the admissible bound
      unfold gammaMax
      rw [lt_div_iff₀ hUI]
      have hlt2 : UC * UI / (2 * UC ^ 2 - UI ^ 2) * UI + UC < Real.sqrt (UC ^ 2 + 3 * UI ^ 2) := by
        rw [Real.lt_sqrt (by positivity)]
        rw [div_mul_eq_mul_div, div_add' _ _ _ hs.ne', div_pow, div_lt_iff₀ (by positivity)]
        have h8 : 0 < (8 * UC ^ 2 - 3 * UI ^ 2) * (UC ^ 2 - UI ^ 2) := by
          have : 0 < UC ^ 2 - UI ^ 2 := by nlinarith
          have : 0 < 8 * UC ^ 2 - 3 * UI ^ 2 := by nlinarith
          positivity
        nlinarith [mul_pos (pow_pos hUI 2) h8]
      linarith
    · intro γ hγ hS n a e hn ha he
      obtain ⟨_, _, hγ0, hγ1, hadm⟩ := hS
      rcases n with ⟨n1, n2⟩
      rcases a with ⟨a1, a2, a3⟩
      rcases e with ⟨e1, e2, e3, e4⟩
      obtain ⟨rfl, rfl⟩ := sq17_ne hn
      obtain ⟨rfl, rfl, rfl⟩ := sq17_acc hγ0 hγ1 ha
      obtain ⟨rfl, rfl, rfl, rfl⟩ := sq17_esc hγ0 hγ1 he
      have hb := sq17_adm hUC hUI hγ0 (hadm.2 hlt)
      have h1g : 0 < 1 - γ := by linarith
      have h2g : 0 < 2 - γ := by linarith
      have hD : 0 < (1 + γ) * (1 - γ) := by positivity
      have hthr : UC * UI < γ * (2 * UC ^ 2 - UI ^ 2) := by
        rw [div_lt_iff₀ hs] at hγ; linarith
      have hc : 0 < 2 * γ * UC ^ 2 - UC * UI - γ * UI ^ 2 := by nlinarith
      set aP : AccPrices := ⟨(2 * UC + γ * UI) / 6, UI / 2, (UC - γ * UI) / 3⟩ with haP
      set nP : NoEntryPrices := ⟨UC / 3, UC / 3⟩ with hnP
      set eP : EscPrices := ⟨((2 - γ) * UC - γ * UI) / (3 * (2 - γ)), UI * (1 - γ) / (2 - γ),
        ((2 - γ) * UC - γ * UI) / (3 * (2 - γ)), UI * (1 - γ) / (2 - γ)⟩ with heP
      have eK : profitA1 UC UI γ aP - profitA0 UC nP
          = γ * (2 * γ * UC ^ 2 - UC * UI - γ * UI ^ 2) / (18 * ((1 + γ) * (1 - γ)))
            + UI * (3 * UI - 2 * γ * UC - γ ^ 2 * UI) / (12 * ((1 + γ) * (1 - γ))) := by
        simp only [haP, hnP, profitA1, profitA0, qC1, qIA1, qC0]
        field_simp
        ring
      have eI : integratedProfitA UC UI γ aP - (profitA1 UC UI γ aP - profitA0 UC nP)
          = -(γ * (2 * γ * UC ^ 2 - UC * UI - γ * UI ^ 2) / (18 * ((1 + γ) * (1 - γ)))) := by
        simp only [haP, hnP, integratedProfitA, profitA1, profitA0, qC1, qIA1, qC0]
        field_simp
        ring
      have eB : profitA1 UC UI γ aP - profitA0 UC nP - profitB2 UC UI γ eP + profitB1 UC UI γ aP
          = γ * (8 * (2 - γ) ^ 2 * (γ * UC - UI) ^ 2
              + UI ^ 2 * (1 - γ) * (2 * γ ^ 3 + 11 * γ ^ 2 + 13 * γ + 4))
            / (36 * (2 - γ) ^ 2 * (1 + γ) * (1 + 2 * γ) * (1 - γ)) := by
        simp only [haP, hnP, heP, profitA1, profitA0, profitB2, profitB1, qC1, qIA1, qC0,
          qC2, qIB2]
        field_simp
        ring
      have hpI : 0 ≤ 3 * UI - 2 * γ * UC - γ ^ 2 * UI := by nlinarith
      have t1 : 0 < γ * (2 * γ * UC ^ 2 - UC * UI - γ * UI ^ 2) / (18 * ((1 + γ) * (1 - γ))) := by
        positivity
      have t2 : 0 ≤ UI * (3 * UI - 2 * γ * UC - γ ^ 2 * UI) / (12 * ((1 + γ) * (1 - γ))) := by
        positivity
      have t3 : 0 < γ * (8 * (2 - γ) ^ 2 * (γ * UC - UI) ^ 2
              + UI ^ 2 * (1 - γ) * (2 * γ ^ 3 + 11 * γ ^ 2 + 13 * γ + 4))
            / (36 * (2 - γ) ^ 2 * (1 + γ) * (1 + 2 * γ) * (1 - γ)) := by
        positivity
      refine ⟨profitA1 UC UI γ aP - profitA0 UC nP, by linarith, ⟨?_, ?_⟩, by linarith⟩
      · unfold benefitA; linarith
      · unfold benefitB; linarith
