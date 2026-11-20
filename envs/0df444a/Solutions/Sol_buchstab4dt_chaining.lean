-- Prove2me | solution 1 for buchstab4dt_chaining
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:44:27.86799+00:00
-- url     : https://prove2.me/submissions/c13d502d-ce68-4ae4-9a70-d8fa34af66d6

import Mathlib
import Definitions.Def_Buchstab4DT_Core
import Theorems.Thm_buchstab4dt_geom
import Theorems.Thm_buchstab4dt_sound4

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

namespace Sol_Buchstab4DT_Chaining

private lemma le_mul_ceilDiv {a b : Nat} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  omega

private lemma setIntegral_prod_symm' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} (f : α × β → ℝ) (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂(μ.prod ν) = ∫ y in t, ∫ x in s, f (x, y) ∂μ ∂ν := by
  have hf' : Integrable f ((μ.restrict s).prod (ν.restrict t)) := by rwa [Measure.prod_restrict]
  rw [← Measure.prod_restrict]
  exact MeasureTheory.integral_prod_symm f hf'

private lemma integrableOn_setIntegral_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} {f : α × β → ℝ} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (fun y => ∫ x in s, f (x, y) ∂μ) t ν := by
  have hf' : Integrable f ((μ.restrict s).prod (ν.restrict t)) := by rwa [Measure.prod_restrict]
  exact hf'.swap.integral_prod_left

private lemma buchstab_nonneg {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) (u : ℝ) : 0 ≤ ω u :=
  buchstab4dt_geom.1 hω u
private lemma buchstab_le_max_inv_two_thirds {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {u : ℝ} (hu : 1 ≤ u) :
    ω u ≤ max (1 / u) (2 / 3) := buchstab4dt_geom.2.1 hω hu
private lemma buchstab_le_one {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) (u : ℝ) : ω u ≤ 1 :=
  buchstab4dt_geom.2.2.1 hω u
private lemma convexOn_inv_prod {E : Type} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : Convex ℝ S) {k : ℕ} (L : Fin k → E → ℝ)
    (haff : ∀ i, ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      L i (a • x + b • y) = a * L i x + b * L i y)
    (hpos : ∀ i, ∀ x ∈ S, 0 < L i x) :
    ConvexOn ℝ S (fun x => (∏ i : Fin k, L i x)⁻¹) :=
  buchstab4dt_geom.2.2.2.1 hS L haff hpos
private lemma hh1_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Icc a b) f) (hcont : ContinuousOn f (Icc a b)) :
    ∫ x in a..b, f x ≤ ((b - a) / 2) * (f a + f b) := buchstab4dt_geom.2.2.2.2.1 hab hconv hcont
private lemma jensen1_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Icc a b) f) (hcont : ContinuousOn f (Icc a b)) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := buchstab4dt_geom.2.2.2.2.2.1 hab hconv hcont
private lemma volume_preserving_equivFin4_3 :
    MeasurePreserving equivFin4_3 (volume : Measure (Fin 4 → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ))) := buchstab4dt_geom.2.2.2.2.2.2.1
private lemma equivFin4_3_apply (x : Fin 4 → ℝ) : equivFin4_3 x = (x 3, ![x 0, x 1, x 2]) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.1 x
private lemma cell4Set_eq_preimage (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 =
      equivFin4_3 ⁻¹' (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2 a3 b3
private lemma cell3Set_isClosed (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    IsClosed (cell3Set knd a0 b0 a1 b1 a2 b2) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2
private lemma cell3Set_isCompact (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    IsCompact (cell3Set knd a0 b0 a1 b1 a2 b2) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2
private lemma cell4Set_isClosed (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    IsClosed (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2 a3 b3
private lemma cell4Set_isCompact (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    IsCompact (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2 a3 b3
private lemma cell3Set_convex (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    Convex ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2
private lemma cell4Set_convex (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    Convex ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd a0 b0 a1 b1 a2 b2 a3 b3
private def integral_cell3_eq_iter (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    {f : (Fin 3 → ℝ) → ℝ} (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd h0 h1 h2 hcont
private def hh_cell3 (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2) {f : (Fin 3 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f)
    (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd hok hconv hcont
private def jensen_cell3 (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2) {f : (Fin 3 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f)
    (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd hok hconv hcont
private def hh_cell4 (knd : CellKind) {a0 b0 a1 b1 a2 b2 a3 b3 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2) (h3 : a3 ≤ b3) {f : (Fin 4 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) f)
    (hcont : ContinuousOn f (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 knd hok h3 hconv hcont
private def integral_ind_le_sub {c h R : ℝ} (hc : 0 < c) (hh : 0 ≤ h) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := R) hc hh
private def vol_cut_box3_eq {a0 b0 a1 b1 a2 b2 L : ℝ} (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (L := L) h0 h1 h2
private def int_ramp_box3_eq {a0 b0 a1 b1 a2 b2 L : ℝ} (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (L := L) h0 h1 h2
private def vol_cut_box4_eq {a0 b0 a1 b1 a2 b2 a3 b3 L : ℝ} (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (L := L) h0 h1 h2 h3
private def volume_fin3_coord_eq_zero (i : Fin 3) (m : ℝ) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i m
private def s3_antitone_le (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2) {g : ℝ → ℝ} (hgnn : ∀ s, 0 ≤ g s) (hganti : Antitone g)
    (hint : IntegrableOn (fun x : Fin 3 → ℝ => g (x 0 + x 1 + 2 * x 2)) (cell3Set .box a0 b0 a1 b1 a2 b2) volume) :=
  buchstab4dt_geom.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 knd hok hgnn hganti hint

private lemma sumVerts3R_le {Dx : ℝ} {gR : (Fin 3 → ℝ) → ℝ} {gN : ℕ → ℕ → ℕ → ℕ} {S : ℝ}
    (knd : CellKind) {n0a n0b n1a n1b n2a n2b : ℕ}
    (ht01 : knd = .tri01 → n0a = n1a ∧ n0b = n1b)
    (ht12 : knd = .tri12 → n1a = n2a ∧ n1b = n2b)
    (hts : knd = .simp → n0a = n1a ∧ n0b = n1b ∧ n1a = n2a ∧ n1b = n2b)
    (hp : ∀ a0 a1 a2 : ℕ, (a0 = n0a ∨ a0 = n0b) → (a1 = n1a ∨ a1 = n1b) → (a2 = n2a ∨ a2 = n2b) →
      gR ![(a0 : ℝ) / Dx, (a1 : ℝ) / Dx, (a2 : ℝ) / Dx] ≤ (gN a0 a1 a2 : ℝ) / S) :
    sumVerts3R gR knd ((n0a : ℝ) / Dx) ((n0b : ℝ) / Dx) ((n1a : ℝ) / Dx) ((n1b : ℝ) / Dx) ((n2a : ℝ) / Dx) ((n2b : ℝ) / Dx) ≤
      (sumVerts3 gN knd n0a n0b n1a n1b n2a n2b : ℝ) / S := by
  cases knd with
  | box =>
    simp only [sumVerts3R, sumVerts3]; push_cast; simp only [add_div]
    gcongr <;> exact hp _ _ _ (by tauto) (by tauto) (by tauto)
  | tri01 =>
    rcases ht01 rfl with ⟨rfl, rfl⟩
    simp only [sumVerts3R, sumVerts3]; push_cast; simp only [add_div]
    gcongr <;> exact hp _ _ _ (by tauto) (by tauto) (by tauto)
  | tri12 =>
    rcases ht12 rfl with ⟨rfl, rfl⟩
    simp only [sumVerts3R, sumVerts3]; push_cast; simp only [add_div]
    gcongr <;> exact hp _ _ _ (by tauto) (by tauto) (by tauto)
  | simp =>
    rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩
    simp only [sumVerts3R, sumVerts3]; push_cast; simp only [add_div]
    gcongr <;> exact hp _ _ _ (by tauto) (by tauto) (by tauto)


private lemma match_cellKind_ne_box {α : Type*} (knd : CellKind)
    (a b : α) :
    knd ≠ .box → (match knd with | .box => a | _ => b) = b := by
  intro hk; cases knd with
  | box => exact absurd rfl hk
  | tri01 => rfl
  | tri12 => rfl
  | simp => rfl

private lemma mm_pos_int_alg (a0 b0 a1 b1 a2 b2 Bn Cn sv Dx fd nv Sv S3 : ℝ)
    (h1 : Dx ≠ 0) (h2 : fd ≠ 0) (h3 : nv ≠ 0) (h4 : Sv ≠ 0) :
    (b0 / Dx - a0 / Dx) * (b1 / Dx - a1 / Dx) * (b2 / Dx - a2 / Dx) / (fd * nv) *
      ((Cn / Dx - Bn / Dx) / 2 * (sv / Sv)) * S3 =
    (S3 * (b0 - a0) * (b1 - a1) * (b2 - a2) * (Cn - Bn) * sv) / (2 * fd * nv * Dx ^ 4 * Sv) := by
  have hsub : ∀ u v : ℝ, v / Dx - u / Dx = (v - u) / Dx := fun u v => (sub_div v u Dx).symm
  rw [hsub a0 b0, hsub a1 b1, hsub a2 b2, hsub Bn Cn]
  field_simp [h1, h2, h3, h4]; try ring

private noncomputable def mpGainFn (p : Params4DT) (pa_n pb_n : ℕ) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b : ℕ) : (Fin 3 → ℝ) → ℝ :=
  let pa : ℝ := (pa_n : ℝ) / p.D_p
  let pb : ℝ := (pb_n : ℝ) / p.D_p
  let s_min_n := p.D_p * (n0a + n1a + 2 * n2a)
  let s_max_n := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let pb_sc := pb_n * p.D_x
  let Pslab : Set (Fin 3 → ℝ) := {y | pa - p.C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - p.B_R}
  let denom_sc := max p.B_sc (pa_sc - s_max_n)
  let gain_c : ℝ := 1 / (((n0a : ℝ) / p.D_x) * ((n1a : ℝ) / p.D_x) * ((n2a : ℝ) / p.D_x) ^ 2 * ((denom_sc : ℝ) / ((p.D_p : ℝ) * p.D_x)))
  if s_max_n + p.C_sc ≤ pa_sc ∨ pb_sc ≤ s_min_n + p.B_sc then fun _ => 0
  else match knd with
    | .box => Pslab.indicator (fun _ => gain_c)
    | _ => fun _ => gain_c

private noncomputable def mpDropFn (p : Params4DT) (pa_n pb_n n0b n1b n2b : ℕ) : (Fin 3 → ℝ) → ℝ :=
  let pb : ℝ := (pb_n : ℝ) / p.D_p
  let s_max_n := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let m_lo_sc := max p.B_sc (min p.C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((p.D_p : ℝ) * p.D_x)
  let xm_r : ℝ := (p.B_R + m_lo_r) / 2
  if m_lo_sc ≤ p.B_sc then fun _ => 0
  else fun y => (m_lo_r - p.B_R) / (y 0 * y 1 * y 2 * xm_r * (pb - (y 0 + y 1 + y 2) - xm_r) ^ 2)

private noncomputable def mmDropFn (p : Params4DT) (pa_n pb_n n0a n0b n1a n1b n2a n2b : ℕ) : (Fin 3 → ℝ) → ℝ :=
  let pa : ℝ := (pa_n : ℝ) / p.D_p
  let pb : ℝ := (pb_n : ℝ) / p.D_p
  let s_min_n := p.D_p * (n0a + n1a + 2 * n2a)
  let s_max_n := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let pb_sc := pb_n * p.D_x
  if pb_sc ≤ s_min_n + p.B_sc then fun _ => 0
  else if s_max_n + p.C_sc ≤ pa_sc then
    fun y => ((p.C_R - p.B_R) / 2) *
      (1 / (y 0 * y 1 * y 2 * p.B_R * (pa - (y 0 + y 1 + y 2) - p.B_R) ^ 2) +
       1 / (y 0 * y 1 * y 2 * p.C_R * (pa - (y 0 + y 1 + y 2) - p.C_R) ^ 2))
  else
    fun y => (max 0 (pb - p.B_R - (y 0 + y 1 + 2 * y 2)) - max 0 (pb - p.C_R - (y 0 + y 1 + 2 * y 2))) /
      (((n0a : ℝ) / p.D_x) * ((n1a : ℝ) / p.D_x) * ((n2a : ℝ) / p.D_x) ^ 3 * p.B_R)

private noncomputable def mmGainFn (p : Params4DT) (pa_n pb_n : ℕ) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b : ℕ) : (Fin 3 → ℝ) → ℝ :=
  let pa : ℝ := (pa_n : ℝ) / p.D_p
  let pb : ℝ := (pb_n : ℝ) / p.D_p
  let s_min_n := p.D_p * (n0a + n1a + 2 * n2a)
  let s_max_n := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let pb_sc := pb_n * p.D_x
  let Pslab_in : Set (Fin 3 → ℝ) := {y | pb - p.C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - p.B_R}
  let denom_x3_sc := min p.C_sc (pb_sc - s_min_n)
  let denom_x2_sc := p.D_p * n2b + (pb_sc - pa_sc)
  let gain_c : ℝ := 1 / (((n0b : ℝ) / p.D_x) * ((n1b : ℝ) / p.D_x) * ((n2b : ℝ) / p.D_x) *
    ((denom_x3_sc : ℝ) / ((p.D_p : ℝ) * p.D_x)) * ((denom_x2_sc : ℝ) / ((p.D_p : ℝ) * p.D_x)))
  if s_max_n + p.C_sc ≤ pb_sc ∨ pa_sc ≤ s_min_n + p.B_sc then fun _ => 0
  else match knd with
    | .box => Pslab_in.indicator (fun _ => gain_c)
    | _ => if pb_sc ≤ s_min_n + p.C_sc ∧ s_max_n + p.B_sc ≤ pa_sc then fun _ => gain_c else fun _ => 0

section

variable {p : Params4DT} (hp : p.Valid)
include hp

local notation "D_x" => p.D_x
local notation "D_p" => p.D_p
local notation "A_n" => p.A_n
local notation "B_n" => p.B_n
local notation "C_n" => p.C_n
local notation "S_v" => p.S_v
local notation "S_3" => p.S_3
local notation "S_4" => p.S_4
local notation "D_x2" => p.D_x2
local notation "D_x4" => p.D_x4
local notation "D_x5" => p.D_x5
local notation "D_x6" => p.D_x6
local notation "D_p2" => p.D_p2
local notation "D_p3" => p.D_p3
local notation "D_p4" => p.D_p4
local notation "B_sc" => p.B_sc
local notation "C_sc" => p.C_sc
local notation "A_R" => p.A_R
local notation "B_R" => p.B_R
local notation "C_R" => p.C_R
local notation "cut3Num" => Buchstab4DT.cut3Num p
local notation "ramp3Num" => Buchstab4DT.ramp3Num p
local notation "cut4Num" => Buchstab4DT.cut4Num p
local notation "eval4Leaf" => Buchstab4DT.eval4Leaf p
local notation "eval4TransLeaf" => Buchstab4DT.eval4TransLeaf p
local notation "evalMpLeaf" => Buchstab4DT.evalMpLeaf p
local notation "evalMmLeaf" => Buchstab4DT.evalMmLeaf p
local notation "cell3Valid" => Buchstab4DT.cell3Valid p
local notation "cell4Valid" => Buchstab4DT.cell4Valid p
local notation "I_fn" => Buchstab4DT.I_fn p
local notation "G_fn" => Buchstab4DT.G_fn p

private lemma hDx_nat_pos : 0 < D_x := hp.1
private lemma hDp_nat_pos : 0 < D_p := hp.2.1
private lemma A_n_pos : 0 < A_n := hp.2.2.1
private lemma hAB_nat : A_n < B_n := hp.2.2.2.1
private lemma hBC_nat : B_n < C_n := hp.2.2.2.2.1
private lemma B_n_pos : 0 < B_n := lt_trans (A_n_pos hp) (hAB_nat hp)
private lemma C_n_pos : 0 < C_n := lt_trans (B_n_pos hp) (hBC_nat hp)
private lemma hSv_nat_pos : 0 < S_v := hp.2.2.2.2.2.1
private lemma hS3_nat_pos : 0 < S_3 := hp.2.2.2.2.2.2.1
private lemma hS4_nat_pos : 0 < S_4 := hp.2.2.2.2.2.2.2.1
private lemma hS4_eq : S_4 = S_3 * 100 := hp.2.2.2.2.2.2.2.2.1
private lemma hDx2_eq : D_x2 = D_x * D_x := hp.2.2.2.2.2.2.2.2.2.1
private lemma hDx4_eq : D_x4 = D_x2 * D_x2 := hp.2.2.2.2.2.2.2.2.2.2.1
private lemma hDx5_eq : D_x5 = D_x4 * D_x := hp.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hDx6_eq : D_x6 = D_x4 * D_x2 := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hDp2_eq : D_p2 = D_p * D_p := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hDp3_eq : D_p3 = D_p2 * D_p := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hDp4_eq : D_p4 = D_p2 * D_p2 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hBsc_eq : B_sc = D_p * B_n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private lemma hCsc_eq : C_sc = D_p * C_n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private lemma hDx2_nat_pos : 0 < D_x2 := by rw [hDx2_eq hp]; exact Nat.mul_pos (hDx_nat_pos hp) (hDx_nat_pos hp)
private lemma hDx4_nat_pos : 0 < D_x4 := by rw [hDx4_eq hp]; exact Nat.mul_pos (hDx2_nat_pos hp) (hDx2_nat_pos hp)
private lemma hDp2_nat_pos : 0 < D_p2 := by rw [hDp2_eq hp]; exact Nat.mul_pos (hDp_nat_pos hp) (hDp_nat_pos hp)
private lemma hDp4_nat_pos : 0 < D_p4 := by rw [hDp4_eq hp]; exact Nat.mul_pos (hDp2_nat_pos hp) (hDp2_nat_pos hp)
private lemma hBsc_nat_pos : 0 < B_sc := by rw [hBsc_eq hp]; exact Nat.mul_pos (hDp_nat_pos hp) (B_n_pos hp)
private lemma hCsc_nat_pos : 0 < C_sc := by rw [hCsc_eq hp]; exact Nat.mul_pos (hDp_nat_pos hp) (C_n_pos hp)
private lemma hDx_pos : (0 : ℝ) < D_x := Nat.cast_pos.mpr (hDx_nat_pos hp)
private lemma hDp_pos : (0 : ℝ) < D_p := Nat.cast_pos.mpr (hDp_nat_pos hp)
private lemma hSv_pos : (0 : ℝ) < S_v := Nat.cast_pos.mpr (hSv_nat_pos hp)
private lemma hS3_pos : (0 : ℝ) < S_3 := Nat.cast_pos.mpr (hS3_nat_pos hp)
private lemma hS4_pos : (0 : ℝ) < S_4 := Nat.cast_pos.mpr (hS4_nat_pos hp)
private lemma D_x2_cast : (D_x2 : ℝ) = (D_x : ℝ) ^ 2 := by rw [hDx2_eq hp, Nat.cast_mul, sq]
private lemma D_x4_cast : (D_x4 : ℝ) = (D_x : ℝ) ^ 4 := by rw [hDx4_eq hp, Nat.cast_mul, D_x2_cast hp]; ring
private lemma D_x5_cast : (D_x5 : ℝ) = (D_x : ℝ) ^ 5 := by rw [hDx5_eq hp, Nat.cast_mul, D_x4_cast hp]; ring
private lemma D_x6_cast : (D_x6 : ℝ) = (D_x : ℝ) ^ 6 := by rw [hDx6_eq hp, Nat.cast_mul, D_x4_cast hp, D_x2_cast hp]; ring
private lemma D_p2_cast : (D_p2 : ℝ) = (D_p : ℝ) ^ 2 := by rw [hDp2_eq hp, Nat.cast_mul, sq]
private lemma D_p3_cast : (D_p3 : ℝ) = (D_p : ℝ) ^ 3 := by rw [hDp3_eq hp, Nat.cast_mul, D_p2_cast hp]; ring
private lemma D_p4_cast : (D_p4 : ℝ) = (D_p : ℝ) ^ 4 := by rw [hDp4_eq hp, Nat.cast_mul, D_p2_cast hp]; ring
private lemma B_sc_le_C_sc : B_sc ≤ C_sc := by rw [hBsc_eq hp, hCsc_eq hp]; exact Nat.mul_le_mul_left _ (le_of_lt (hBC_nat hp))
private lemma B_sc_cast : (B_sc : ℝ) = (D_p : ℝ) * B_n := by rw [hBsc_eq hp, Nat.cast_mul]
private lemma C_sc_cast : (C_sc : ℝ) = (D_p : ℝ) * C_n := by rw [hCsc_eq hp, Nat.cast_mul]
private lemma hA_pos : (0 : ℝ) < A_R := div_pos (Nat.cast_pos.mpr (A_n_pos hp)) (hDx_pos hp)
private lemma hAB_lt : A_R < B_R := div_lt_div_of_pos_right (Nat.cast_lt.mpr (hAB_nat hp)) (hDx_pos hp)
private lemma hBC_lt : B_R < C_R := div_lt_div_of_pos_right (Nat.cast_lt.mpr (hBC_nat hp)) (hDx_pos hp)


private lemma cut3Num_eq : ∀ {dx0 dx1 dx2 r : ℕ},
    ((cut3Num dx0 dx1 dx2 r : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3)) =
      cut3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 12 :=
  (buchstab4dt_sound4 p hp).1
private lemma ramp3Num_eq : ∀ {dx0 dx1 dx2 r : ℕ},
    ((ramp3Num dx0 dx1 dx2 r : ℝ) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4)) =
      ramp3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 48 :=
  (buchstab4dt_sound4 p hp).2.1
private def cell3Valid_ok {knd n0a n0b n1a n1b n2a n2b} (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :=
  (buchstab4dt_sound4 p hp).2.2.1 hv
private def cell4_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {p_n : ℕ}
    (ht : (p_n : ℝ) / D_p ≤ 5 * A_R + B_R) {knd n0a n0b n1a n1b n2a n2b n3a n3b}
    (hv : cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b) :=
  (buchstab4dt_sound4 p hp).2.2.2.1 hω ht hv
private def cell4_trans_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {pa_n : ℕ} {φ : ℝ}
    (hlo : (pa_n : ℝ) / D_p ≤ φ) (hge : D_p * (4 * B_n + C_n) ≤ pa_n * D_x)
    {knd n0a n0b n1a n1b n2a n2b n3a n3b} (hv : cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b) :=
  (buchstab4dt_sound4 p hp).2.2.2.2.1 hω hlo hge hv
private def evalTree4_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) :=
  (buchstab4dt_sound4 p hp).2.2.2.2.2.1 hω
private def I_fn_eq_G {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {φ : ℝ} (ht : φ ≤ 5 * A_R + B_R) :=
  (buchstab4dt_sound4 p hp).2.2.2.2.2.2.1 hω ht
private def G_fn_sub_eq {φ1 φ2 : ℝ} (h12 : φ1 < φ2) {y : Fin 3 → ℝ} (hy2 : 0 < y 2) :=
  (buchstab4dt_sound4 p hp).2.2.2.2.2.2.2.1 h12 hy2
private def G_fn_integrableOn {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {φ : ℝ} (ht : φ ≤ 5 * A_R + B_R)
    {knd n0a n0b n1a n1b n2a n2b} (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :=
  (buchstab4dt_sound4 p hp).2.2.2.2.2.2.2.2.1 hω ht hv
private def evalTree3_sound {F : (Fin 3 → ℝ) → ℝ} :=
  (buchstab4dt_sound4 p hp).2.2.2.2.2.2.2.2.2 (F := F)

/-! ### Part 6E: Leaf Soundness for `evalMpLeaf` and `evalMmLeaf` -/

private lemma mp_m_lo_props {pa_n : ℕ} {φ1 : ℝ} (hpa_le : (pa_n : ℝ) / D_p ≤ φ1)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    (hlt : B_sc < max B_sc (min C_sc (pa_n * D_x - D_p * (n0b + n1b + 2 * n2b)))) :
    let m_lo_r : ℝ := ((max B_sc (min C_sc (pa_n * D_x - D_p * (n0b + n1b + 2 * n2b))) : ℕ) : ℝ) / ((D_p : ℝ) * D_x)
    B_R < m_lo_r ∧ m_lo_r ≤ C_R ∧
    (∀ y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      m_lo_r ≤ φ1 - y 0 - y 1 - 2 * y 2) := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set m_lo_sc := max B_sc (min C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((D_p : ℝ) * D_x)
  have h1 : B_R < m_lo_r := by
    have : (B_sc : ℝ) < m_lo_sc := by exact_mod_cast hlt
    dsimp only [m_lo_r, Params4DT.B_R]; rw [(B_sc_cast hp)] at this
    rw [div_lt_div_iff₀ hDx (mul_pos hDp hDx)]; nlinarith
  have h2 : m_lo_r ≤ C_R := by
    have : m_lo_sc ≤ C_sc := max_le (B_sc_le_C_sc hp) (min_le_left _ _)
    have hr : (m_lo_sc : ℝ) ≤ C_sc := by exact_mod_cast this
    dsimp only [m_lo_r, Params4DT.C_R]; rw [(C_sc_cast hp)] at hr
    rw [div_le_div_iff₀ (mul_pos hDp hDx) hDx]; nlinarith
  have h3 : ∀ y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      m_lo_r ≤ φ1 - y 0 - y 1 - 2 * y 2 := by
    intro y hy
    have hmem : y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧ y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧ y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
      cases knd with
      | box => exact hy
      | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    rcases hmem with ⟨hy0, hy1, hy2⟩
    have hmlo_le_diff : m_lo_sc ≤ pa_sc - s_max_n := by
      have heq : m_lo_sc = min C_sc (pa_sc - s_max_n) := max_eq_right (by by_contra hlt'; push Not at hlt'; exact ne_of_gt hlt (max_eq_left (le_of_lt hlt')))
      rw [heq]; exact min_le_right _ _
    have hs_lt_pa : s_max_n < pa_sc := by
      have : 0 < m_lo_sc := lt_of_le_of_lt (Nat.zero_le _) hlt
      omega
    have hle_r : (m_lo_sc : ℝ) ≤ (pa_sc : ℝ) - s_max_n := by
      have : (m_lo_sc : ℝ) ≤ ((pa_sc - s_max_n : ℕ) : ℝ) := by exact_mod_cast hmlo_le_diff
      rwa [Nat.cast_sub (le_of_lt hs_lt_pa)] at this
    have hdiff_r : m_lo_r ≤ pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x)) := by
      dsimp only [m_lo_r, pa, pa_sc, s_max_n] at hle_r ⊢; push_cast at hle_r
      have : (pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
          (pa_n : ℝ) * D_x - (D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) := by
        dsimp only [pa]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      rw [div_le_iff₀ (mul_pos hDp hDx)]; linarith
    linarith [hpa_le, hy0.2, hy1.2, hy2.2]
  exact ⟨h1, h2, h3⟩

private lemma mpDropFn_continuousOn {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ContinuousOn (mpDropFn p pa_n pb_n n0b n1b n2b)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) := by
  have hDx := (hDx_pos hp)
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hv' := hv
  rcases hv with ⟨hA0, _, h0B, hA1, _, h1B, hA2, _, h2B, ht01, ht12, hts⟩
  unfold mpDropFn; dsimp only; split_ifs with hmlo_z
  · exact continuousOn_const
  · push Not at hmlo_z
    rcases mp_m_lo_props hp hpa_le hv' hmlo_z with ⟨hB_lt_m, _, hm_le_cut⟩
    refine continuousOn_const.div (by fun_prop) ?_
    intro y hy
    have hmem : y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧ y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧ y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
      cases knd with
      | box => exact hy
      | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    have : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) hmem.1.1)
    have : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) hmem.2.1.1)
    have : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) hmem.2.2.1)
    have : 0 < (B_R + ((max B_sc (min C_sc (pa_n * D_x - D_p * (n0b + n1b + 2 * n2b))) : ℕ) : ℝ) / ((D_p : ℝ) * D_x)) / 2 := by linarith
    have : 0 < (pb_n : ℝ) / D_p - (y 0 + y 1 + y 2) - (B_R + ((max B_sc (min C_sc (pa_n * D_x - D_p * (n0b + n1b + 2 * n2b))) : ℕ) : ℝ) / ((D_p : ℝ) * D_x)) / 2 := by
      linarith [hm_le_cut y hy, h12, hpb_ge]
    positivity

private lemma cell3_Mp_pt_gain {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    {y : Fin 3 → ℝ}
    (hy : y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :
    ((1 / (y 0 * y 1 * y 2)) *
      (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) ≤
      mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y := by
  have hv' := hv
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab : Set (Fin 3 → ℝ) := {y | pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R}
  set denom_sc := max B_sc (pa_sc - s_max_n)
  have hdenom_pos : 0 < denom_sc := lt_of_lt_of_le ((hBsc_nat_pos hp)) (le_max_left _ _)
  let gain_c : ℝ := 1 / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((denom_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  set m_lo_sc := max B_sc (min C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((D_p : ℝ) * D_x)
  let xm_r : ℝ := (B_R + m_lo_r) / 2
  let drop_fn : (Fin 3 → ℝ) → ℝ := mpDropFn p pa_n pb_n n0b n1b n2b
  have hm_lo_props : B_sc < m_lo_sc → B_R < m_lo_r ∧ m_lo_r ≤ C_R ∧ (∀ y ∈ C, m_lo_r ≤ φ1 - y 0 - y 1 - 2 * y 2) :=
    mp_m_lo_props hp hpa_le hv'
  rcases hmem y hy with ⟨hy0, hy1, hy2⟩
  rcases hmem_simp y hy with ⟨hA0y, hA1y, hA2y⟩
  have hy0p : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hA0y.1
  have hy1p : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hA1y.1
  have hy2p : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hA2y.1
  set m1 := max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))
  set m2 := max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))
  have hBm1 : B_R ≤ m1 := le_max_left _ _
  have hm12 : m1 ≤ m2 := max_le_max_left B_R (min_le_min_left C_R (by linarith))
  have hBm2 : B_R ≤ m2 := le_trans hBm1 hm12
  -- Bound Part A: gain term ≤ gain_fn y
  have hgain_le : ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) ≤ gain_fn y := by
    by_cases hm12_eq : m1 = m2
    · rw [hm12_eq, intervalIntegral.integral_same, mul_zero, zero_div]
      have hgc_nn : 0 ≤ gain_c := by
        dsimp only [gain_c]
        exact div_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg
          (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))
          (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))) (sq_nonneg _))
          (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hDp) (le_of_lt hDx))))
      dsimp only [gain_fn, mpGainFn]; split_ifs
      · exact le_refl 0
      · cases knd with
        | box => exact Set.indicator_nonneg (fun _ _ => hgc_nn) y
        | _ => exact hgc_nn
    · have hm1_lt_m2 : m1 < m2 := lt_of_le_of_ne hm12 hm12_eq
      -- Since m1 < m2, we MUST have φ1 - y0 - y1 - 2*y2 < C_R AND B_R < φ2 - y0 - y1 - 2*y2!
      have hy_slab : pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R := by
        constructor
        · by_contra hle; push Not at hle
          have h1 : C_R ≤ φ1 - y 0 - y 1 - 2 * y 2 := by linarith
          have hm1c : m1 = C_R := by dsimp only [m1]; rw [min_eq_left h1, max_eq_right (le_of_lt (hBC_lt hp))]
          have hm2c : m2 = C_R := by dsimp only [m2]; rw [min_eq_left (by linarith), max_eq_right (le_of_lt (hBC_lt hp))]
          exact hm12_eq (hm1c.trans hm2c.symm)
        · by_contra hgt; push Not at hgt
          have h2 : φ2 - y 0 - y 1 - 2 * y 2 < B_R := by linarith
          have hm2b : m2 = B_R := by dsimp only [m2]; exact max_eq_left (le_trans (min_le_right _ _) (le_of_lt h2))
          have hm1b : m1 = B_R := le_antisymm (hm2b ▸ hm12) hBm1
          exact hm12_eq (hm1b.trans hm2b.symm)
      have hnot_zero : ¬ (s_max_n + C_sc ≤ pa_sc ∨ pb_sc ≤ s_min_n + B_sc) := by
        rintro (h1 | h2)
        · have hr : (n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R ≤ pa := by
            have h1' : ((s_max_n + C_sc : ℕ) : ℝ) ≤ (pa_sc : ℝ) := by exact_mod_cast h1
            dsimp only [s_max_n, pa_sc] at h1'; push_cast [(C_sc_cast hp)] at h1'
            dsimp only [pa, Params4DT.C_R]; rw [le_div_iff₀ hDp]
            have : ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + (C_n : ℝ) / D_x) * D_p * D_x =
                (D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * C_n := by field_simp [ne_of_gt hDx]; try ring
            nlinarith [hDx]
          linarith [hy_slab.1, hy0.2, hy1.2, hy2.2]
        · have hr : pb ≤ (n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + B_R := by
            have h2' : (pb_sc : ℝ) ≤ ((s_min_n + B_sc : ℕ) : ℝ) := by exact_mod_cast h2
            dsimp only [s_min_n, pb_sc] at h2'; push_cast [(B_sc_cast hp)] at h2'
            dsimp only [pb, Params4DT.B_R]; rw [div_le_iff₀ hDp]
            have : ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + (B_n : ℝ) / D_x) * D_p * D_x =
                (D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a) + (D_p : ℝ) * B_n := by field_simp [ne_of_gt hDx]; try ring
            nlinarith [hDx]
          -- Wait: if y0 + y1 + 2*y2 = pb - B_R, then φ2 - y0 - y1 - 2*y2 ≤ B_R so m2 = B_R = m1!
          have hlt_strict : y 0 + y 1 + 2 * y 2 < pb - B_R := by
            by_contra hge; push Not at hge
            have h2' : φ2 - y 0 - y 1 - 2 * y 2 ≤ B_R := by linarith
            have hm2b : m2 = B_R := max_eq_left (le_trans (min_le_right _ _) h2')
            exact hm12_eq ((le_antisymm (hm2b ▸ hm12) hBm1).trans hm2b.symm)
          linarith [hlt_strict, hy0.1, hy1.1, hy2.1]
      have hgain_val : gain_fn y = gain_c := by
        dsimp only [gain_fn, mpGainFn]; rw [if_neg hnot_zero]
        cases knd with
        | box => exact Set.indicator_of_mem (show y ∈ Pslab from hy_slab) _
        | _ => rfl
      rw [hgain_val]
      -- Bound ∫_{m1}^{m2} 1/(x3*(φ2-S-x3)) ≤ (m2 - m1) / (denom_r * y2) ≤ (φ2 - φ1) / (denom_r * y2)!
      have hm2_sub_m1 : m2 - m1 ≤ φ2 - φ1 := by
        -- max B (min C u) is 1-Lipschitz in u!
        have hmin : min C_R (φ2 - y 0 - y 1 - 2 * y 2) - min C_R (φ1 - y 0 - y 1 - 2 * y 2) ≤ φ2 - φ1 := by
          rcases min_cases C_R (φ1 - y 0 - y 1 - 2 * y 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          · linarith [min_le_left C_R (φ2 - y 0 - y 1 - 2 * y 2)]
          · linarith [min_le_right C_R (φ2 - y 0 - y 1 - 2 * y 2)]
        rcases max_cases B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2)) with ⟨h, _⟩ | ⟨h, _⟩
        · dsimp only [m2]; rw [h]; linarith [le_max_left B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))]
        · dsimp only [m2]; rw [h]; linarith [le_max_right B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))]
      have hm2_le_cut : m2 ≤ φ2 - y 0 - y 1 - 2 * y 2 := by
        have hm2B : m2 ≠ B_R := fun h => hm12_eq ((le_antisymm (h ▸ hm12) hBm1).trans h.symm)
        have : m2 = min C_R (φ2 - y 0 - y 1 - 2 * y 2) :=
          max_eq_right (by by_contra hlt; push Not at hlt; exact hm2B (max_eq_left (le_of_lt hlt)))
        rw [this]; exact min_le_right _ _
      have hdenom_le_m1 : (denom_sc : ℝ) / ((D_p : ℝ) * D_x) ≤ m1 := by
        dsimp only [denom_sc]
        by_cases hmx : B_sc ≥ pa_sc - s_max_n
        · rw [max_eq_left hmx]
          have : (B_sc : ℝ) / ((D_p : ℝ) * D_x) = B_R := by rw [(B_sc_cast hp)]; dsimp only [Params4DT.B_R]; field_simp [ne_of_gt hDp]
          rw [this]; exact hBm1
        · push Not at hmx
          rw [max_eq_right (le_of_lt hmx)]
          have hlt_pa : s_max_n < pa_sc := by
            have : 0 < pa_sc - s_max_n := lt_of_le_of_lt (Nat.zero_le _) hmx; omega
          have heq : ((pa_sc - s_max_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) =
              pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x)) := by
            rw [Nat.cast_sub (le_of_lt hlt_pa)]; dsimp only [pa_sc, s_max_n, pa]; push_cast
            field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          rw [heq]
          have hlt_C : pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x)) < C_R := by
            have h1 : ¬ (s_max_n + C_sc ≤ pa_sc) := fun h => hnot_zero (Or.inl h)
            have h1' : (pa_sc : ℝ) < ((s_max_n + C_sc : ℕ) : ℝ) := by exact_mod_cast (show pa_sc < s_max_n + C_sc by omega)
            dsimp only [pa_sc, s_max_n] at h1'; push_cast [(C_sc_cast hp)] at h1'
            dsimp only [pa, Params4DT.C_R]
            have : (pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x)) - (C_n : ℝ) / D_x) * ((D_p : ℝ) * D_x) =
                (pa_n : ℝ) * D_x - ((D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * C_n) := by
              have hgen : ∀ (P a b c d Dp Dx : ℝ), Dp ≠ 0 → Dx ≠ 0 →
                  (P / Dp - (a / Dx + b / Dx + 2 * (c / Dx)) - d / Dx) * (Dp * Dx) = P * Dx - (Dp * (a + b + 2 * c) + Dp * d) := by
                intro P a b c d Dp Dx h1 h2; field_simp [h1, h2]; ring
              exact hgen pa_n n0b n1b n2b C_n D_p D_x (ne_of_gt hDp) (ne_of_gt hDx)
            exact sub_neg.mp (neg_of_mul_neg_left (by rw [this]; exact sub_neg.mpr h1') (le_of_lt (mul_pos hDp hDx)))
          exact le_trans (le_min (le_of_lt hlt_C) (by linarith only [hpa_le, hy0.2, hy1.2, hy2.2])) (le_max_right _ _)
      have hden_r_pos : 0 < (denom_sc : ℝ) / ((D_p : ℝ) * D_x) := div_pos (by exact_mod_cast hdenom_pos) (mul_pos hDp hDx)
      have hc2 : ContinuousOn (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc m1 m2) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le (lt_of_lt_of_le hBpos hBm1) hx3.1
          have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm2_le_cut]

          positivity)
      have hint_le : ∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)) ≤
          (m2 - m1) * (1 / (((denom_sc : ℝ) / ((D_p : ℝ) * D_x)) * y 2)) := by
        have hmono := intervalIntegral.integral_mono_on hm12 (hc2.intervalIntegrable_of_Icc hm12) (intervalIntegrable_const : IntervalIntegrable (fun _ => 1 / (((denom_sc : ℝ) / ((D_p : ℝ) * D_x)) * y 2)) volume m1 m2)
          (fun x3 hx3 => by
            have hx3_ge : (denom_sc : ℝ) / ((D_p : ℝ) * D_x) ≤ x3 := le_trans hdenom_le_m1 hx3.1
            have hrem_ge : y 2 ≤ φ2 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm2_le_cut]
            exact div_le_div₀ (by norm_num) (le_refl 1) (mul_pos hden_r_pos hy2p)
              (mul_le_mul hx3_ge hrem_ge (le_of_lt hy2p) (le_trans (le_of_lt hden_r_pos) hx3_ge)))
        rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have hstep1 : ∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)) ≤
          (φ2 - φ1) * (1 / (((denom_sc : ℝ) / ((D_p : ℝ) * D_x)) * y 2)) :=
        le_trans hint_le (mul_le_mul_of_nonneg_right hm2_sub_m1 (by positivity))
      have hstep2 : ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) ≤
          1 / (y 0 * y 1 * y 2 ^ 2 * ((denom_sc : ℝ) / ((D_p : ℝ) * D_x))) := by
        rw [div_le_iff₀ h12pos]
        have hmul := mul_le_mul_of_nonneg_left hstep1 (show (0 : ℝ) ≤ 1 / (y 0 * y 1 * y 2) by positivity)
        refine le_trans hmul (le_of_eq ?_); field_simp [ne_of_gt hy0p, ne_of_gt hy1p, ne_of_gt hy2p, ne_of_gt hden_r_pos]; try ring
      refine le_trans hstep2 ?_
      dsimp only [gain_c]
      have h0a_p : (0 : ℝ) < (n0a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h0p) hDx
      have h1a_p : (0 : ℝ) < (n1a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h1p) hDx
      have h2a_p : (0 : ℝ) < (n2a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h2p) hDx
      refine div_le_div₀ (by norm_num) (le_refl 1) (by positivity) ?_
      have h01 := mul_le_mul hy0.1 hy1.1 (le_of_lt h1a_p) (le_trans (le_of_lt h0a_p) hy0.1)
      have h22 : ((n2a : ℝ) / D_x) ^ 2 ≤ y 2 ^ 2 := by rw [sq, sq]; exact mul_le_mul hy2.1 hy2.1 (le_of_lt h2a_p) (le_trans (le_of_lt h2a_p) hy2.1)
      have h0122 := mul_le_mul h01 h22 (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right h0122 (le_of_lt hden_r_pos)
  exact hgain_le

private lemma cell3_Mp_pt_drop {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    {y : Fin 3 → ℝ}
    (hy : y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :
    mpDropFn p pa_n pb_n n0b n1b n2b y ≤
      (1 / (y 0 * y 1 * y 2)) *
        (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
          1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) := by
  have hv' := hv
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab : Set (Fin 3 → ℝ) := {y | pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R}
  set denom_sc := max B_sc (pa_sc - s_max_n)
  have hdenom_pos : 0 < denom_sc := lt_of_lt_of_le ((hBsc_nat_pos hp)) (le_max_left _ _)
  let gain_c : ℝ := 1 / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((denom_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  set m_lo_sc := max B_sc (min C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((D_p : ℝ) * D_x)
  let xm_r : ℝ := (B_R + m_lo_r) / 2
  let drop_fn : (Fin 3 → ℝ) → ℝ := mpDropFn p pa_n pb_n n0b n1b n2b
  have hm_lo_props : B_sc < m_lo_sc → B_R < m_lo_r ∧ m_lo_r ≤ C_R ∧ (∀ y ∈ C, m_lo_r ≤ φ1 - y 0 - y 1 - 2 * y 2) :=
    mp_m_lo_props hp hpa_le hv'
  rcases hmem y hy with ⟨hy0, hy1, hy2⟩
  rcases hmem_simp y hy with ⟨hA0y, hA1y, hA2y⟩
  have hy0p : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hA0y.1
  have hy1p : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hA1y.1
  have hy2p : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hA2y.1
  set m1 := max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))
  set m2 := max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))
  have hBm1 : B_R ≤ m1 := le_max_left _ _
  have hm12 : m1 ≤ m2 := max_le_max_left B_R (min_le_min_left C_R (by linarith))
  have hBm2 : B_R ≤ m2 := le_trans hBm1 hm12
  -- Bound Part B: drop_fn y ≤ (1/(y0*y1*y2)) * ∫_{B_R}^{m1} 1/(x3*(R1-x3)*(R2-x3))
  have hdrop_le : drop_fn y ≤ (1 / (y 0 * y 1 * y 2)) *
      ∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) := by
    dsimp only [drop_fn, mpDropFn]; split_ifs with hmlo_z
    · by_cases hm1B : m1 = B_R
      · rw [hm1B, intervalIntegral.integral_same, mul_zero]
      · apply mul_nonneg (by positivity)
        apply intervalIntegral.integral_nonneg hBm1
        intro x3 hx3
        have hx3p : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
        have hm1_le_cut : m1 ≤ φ1 - y 0 - y 1 - 2 * y 2 := by
          have : m1 = min C_R (φ1 - y 0 - y 1 - 2 * y 2) :=
            max_eq_right (by by_contra hlt; push Not at hlt; exact hm1B (max_eq_left (le_of_lt hlt)))
          rw [this]; exact min_le_right _ _
        have hr1 : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith only [hx3.2, hm1_le_cut, hy2p]
        have hr2 : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith only [h12, hr1]
        positivity
    · push Not at hmlo_z
      rcases hm_lo_props hmlo_z with ⟨hB_lt_m, hm_le_C, hm_le_cut⟩
      have hm_le_m1 : m_lo_r ≤ m1 := le_trans (le_min hm_le_C (hm_le_cut y hy)) (le_max_right _ _)
      have hm1_le_cut : m1 ≤ φ1 - y 0 - y 1 - 2 * y 2 := by
        have hm1B : m1 ≠ B_R := ne_of_gt (lt_of_lt_of_le hB_lt_m hm_le_m1)
        have : m1 = min C_R (φ1 - y 0 - y 1 - 2 * y 2) :=
          max_eq_right (by by_contra hlt; push Not at hlt; exact hm1B (max_eq_left (le_of_lt hlt)))
        rw [this]; exact min_le_right _ _
      -- Restrict B_R..m1 to B_R..m_lo_r, bound integrand below by 1/(x3*(pb-S-x3)^2), apply jensen1_Icc!
      have hc_drop : ContinuousOn (fun x3 => 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc B_R m1) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
          have hr1' : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith only [hx3.2, hm1_le_cut, hy2p]
          have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith only [h12, hr1']

          positivity)
      have hi_all : IntervalIntegrable _ volume B_R m1 := hc_drop.intervalIntegrable_of_Icc hBm1
      have hi_l := hi_all.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hBm1]; exact ⟨le_of_lt hB_lt_m, hm_le_m1⟩))
      have hi_r := hi_all.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hBm1]; exact ⟨le_of_lt hB_lt_m, hm_le_m1⟩))
      rw [← intervalIntegral.integral_add_adjacent_intervals hi_l hi_r]
      have hr_nn : 0 ≤ ∫ x3 in m_lo_r..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) := by
        apply intervalIntegral.integral_nonneg hm_le_m1
        intro x3 hx3
        have : 0 < x3 := lt_of_lt_of_le (lt_trans hBpos hB_lt_m) hx3.1
        have : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm1_le_cut]
        have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith

        positivity
      have hc_pb : ContinuousOn (fun x3 => 1 / (x3 * (pb - (y 0 + y 1 + y 2) - x3) ^ 2)) (Icc B_R m_lo_r) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
          have : 0 < pb - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm_le_cut y hy, h12, hpb_ge]

          positivity)
      have hconv_pb : ConvexOn ℝ (Icc B_R m_lo_r) (fun x3 => 1 / (x3 * (pb - (y 0 + y 1 + y 2) - x3) ^ 2)) := by
        let L : Fin 3 → ℝ → ℝ := ![fun t => t, fun t => pb - (y 0 + y 1 + y 2) - t, fun t => pb - (y 0 + y 1 + y 2) - t]
        have hfeq : (fun x3 : ℝ => 1 / (x3 * (pb - (y 0 + y 1 + y 2) - x3) ^ 2)) = fun t => (∏ i : Fin 3, L i t)⁻¹ := by
          ext t; dsimp only [L]; rw [Fin.prod_univ_three, one_div, sq]; simp; ring
        rw [hfeq]
        refine convexOn_inv_prod (convex_Icc B_R m_lo_r) L
          (fun i _ _ _ _ a b _ _ hab => by have ha1 : a = 1 - b := (by linarith only [hab]); fin_cases i <;> simp [L, smul_eq_mul] <;> (rw [ha1]; ring)) ?_
        intro i t ht; fin_cases i <;> dsimp only [L]
        · exact lt_of_lt_of_le hBpos ht.1
        · change 0 < pb - (y 0 + y 1 + y 2) - t; linarith [ht.2, hm_le_cut y hy, h12, hpb_ge]
        · change 0 < pb - (y 0 + y 1 + y 2) - t; linarith [ht.2, hm_le_cut y hy, h12, hpb_ge]
      have hj1 := jensen1_Icc (le_of_lt hB_lt_m) hconv_pb hc_pb
      have hmono_l : ∫ x3 in B_R..m_lo_r, 1 / (x3 * (pb - (y 0 + y 1 + y 2) - x3) ^ 2) ≤
          ∫ x3 in B_R..m_lo_r, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) := by
        apply intervalIntegral.integral_mono_on (le_of_lt hB_lt_m) (hc_pb.intervalIntegrable_of_Icc (le_of_lt hB_lt_m)) hi_l
        intro x3 hx3
        have hx3p : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
        have hr1 : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm_le_cut y hy]
        have hr2 : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith
        have hle_den : x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3) ≤
            x3 * (pb - (y 0 + y 1 + y 2) - x3) ^ 2 := by
          rw [sq, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (by linarith) (le_of_lt hr2) (by linarith)) (le_of_lt hx3p)
        exact div_le_div₀ (by norm_num) (le_refl 1) (by positivity) hle_den
      have hstep : (m_lo_r - B_R) * (1 / (xm_r * (pb - (y 0 + y 1 + y 2) - xm_r) ^ 2)) ≤
          ∫ x3 in B_R..m_lo_r, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) :=
        le_trans hj1 hmono_l
      have hmul := mul_le_mul_of_nonneg_left (le_trans hstep (le_add_of_nonneg_right hr_nn)) (show (0 : ℝ) ≤ 1 / (y 0 * y 1 * y 2) by positivity)
      refine le_trans (le_of_eq ?_) hmul
      change (m_lo_r - B_R) / (y 0 * y 1 * y 2 * xm_r * (pb - (y 0 + y 1 + y 2) - xm_r) ^ 2) = _
      simp only [div_eq_mul_inv, one_mul, mul_inv]; ring
  exact hdrop_le

private lemma cell3_Mp_pt {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ∀ y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1) ≤
        mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y - mpDropFn p pa_n pb_n n0b n1b n2b y := by
  intro y hy
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hy2p : 0 < y 2 := by
    rcases hv with ⟨_, _, _, _, _, _, hA2, _, _, ht01, ht12, hts⟩
    have hmem2 : (n2a : ℝ) / D_x ≤ y 2 := by
      cases knd with
      | box => exact hy.2.2.1
      | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact hy.2.2.1.1
      | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact hy.2.2.1.1
      | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact hy.2.2.1.1
    exact lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt (hDx_pos hp))) hmem2)
  have hsub := G_fn_sub_eq hp h12 hy2p
  dsimp only at hsub
  rw [hsub]
  have hsplit : ((1 / (y 0 * y 1 * y 2)) *
      ((∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
          1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) -
       (φ2 - φ1) * (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
          1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))))) / (φ2 - φ1) =
      ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) -
      (1 / (y 0 * y 1 * y 2)) * (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) := by
    field_simp [ne_of_gt h12pos]
  rw [hsplit]
  have hg := cell3_Mp_pt_gain hp hpa_le h12 hpb_ge hv hy
  have hd := cell3_Mp_pt_drop hp hpa_le h12 hpb_ge hv hy
  linarith only [hg, hd]

private lemma cell3_Mp_pos_bound {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y ≤
      ((evalMpLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b).1 : ℝ) / S_3 := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab : Set (Fin 3 → ℝ) := {y | pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R}
  set denom_sc := max B_sc (pa_sc - s_max_n)
  have hdenom_pos : 0 < denom_sc := lt_of_lt_of_le ((hBsc_nat_pos hp)) (le_max_left _ _)
  let gain_c : ℝ := 1 / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((denom_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  set m_lo_sc := max B_sc (min C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((D_p : ℝ) * D_x)
  let xm_r : ℝ := (B_R + m_lo_r) / 2
  let drop_fn : (Fin 3 → ℝ) → ℝ := mpDropFn p pa_n pb_n n0b n1b n2b
  dsimp only [Buchstab4DT.evalMpLeaf, mpGainFn]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hcond : s_max_n + C_sc ≤ pa_sc ∨ pb_sc ≤ s_min_n + B_sc
  · rw [if_pos hcond, if_pos hcond]; simp
  · rw [if_neg hcond, if_neg hcond]
    have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
    have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
    have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
    by_cases hk : knd = .box
    · subst hk
      change ∫ y in C, Pslab.indicator (fun _ => gain_c) y ≤ _
      -- Exact cut3 difference on box!
      have hind_eq : ∀ y : Fin 3 → ℝ, Pslab.indicator (fun _ => gain_c) y =
          gain_c * (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - B_R}).indicator (fun _ => (1 : ℝ)) y -
                    ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - C_R}).indicator (fun _ => (1 : ℝ)) y) := by
        intro y; simp only [Pslab, Set.indicator, mem_ofPred_eq]
        have hpaC_le_pbB : pa - C_R ≤ pb - B_R := by
          have : pa ≤ pb := by linarith
          linarith [(hBC_lt hp)]
        by_cases h1 : y 0 + y 1 + 2 * y 2 ≤ pb - B_R
        · by_cases h2 : y 0 + y 1 + 2 * y 2 ≤ pa - C_R
          · have hn : ¬ (pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R) := fun h => not_lt_of_ge h2 h.1
            simp [h1, h2, hn]
          · have hy' : pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R := ⟨lt_of_not_ge h2, h1⟩
            simp [h1, h2, hy']
        · have h2 : ¬ (y 0 + y 1 + 2 * y 2 ≤ pa - C_R) := fun h => h1 (le_trans h hpaC_le_pbB)
          have hn : ¬ (pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R) := fun h => h1 h.2
          simp [h1, h2, hn]
      simp_rw [hind_eq]
      have hi_hi : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - B_R}).indicator (fun _ => (1 : ℝ))) C volume :=
        (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator
          (isClosed_le (by fun_prop) continuous_const).measurableSet
      have hi_lo : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - C_R}).indicator (fun _ => (1 : ℝ))) C volume :=
        (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator
          (isClosed_le (by fun_prop) continuous_const).measurableSet
      rw [integral_const_mul, integral_sub hi_hi hi_lo,
          vol_cut_box3_eq h0le_r h1le_r h2le_r, vol_cut_box3_eq h0le_r h1le_r h2le_r]
      have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
      rw [hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le]
      push Not at hcond
      have hR1 : pb - B_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
          ((pb_sc - B_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
        have hge : s_min_n + B_sc ≤ pb_sc := le_of_lt hcond.2
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        dsimp only [pb, Params4DT.B_R, pb_sc, s_min_n]; push_cast [(B_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      have hR2_le : cut3SumR (((n0b - n0a : ℕ) : ℝ) / D_x) (((n1b - n1a : ℕ) : ℝ) / D_x) (2 * (((n2b - n2a : ℕ) : ℝ) / D_x))
          (pa - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) / 12 =
          (cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pa_sc - C_sc - s_min_n) : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) := by
        by_cases hge2 : C_sc + s_min_n ≤ pa_sc
        · have hR2 : pa - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
              ((pa_sc - C_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            dsimp only [pa, Params4DT.C_R, pa_sc, s_min_n]; push_cast [(C_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          rw [hR2, ← cut3Num_eq hp]
        · push Not at hge2
          have hz_n : pa_sc - C_sc - s_min_n = 0 := by omega
          rw [hz_n]; simp only [Buchstab4DT.cut3Num, beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div]
          have hneg : pa - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) ≤ 0 := by
            have hlt : (pa_sc : ℝ) < ((C_sc + s_min_n : ℕ) : ℝ) := by exact_mod_cast hge2
            dsimp only [pa_sc, s_min_n] at hlt; push_cast [(C_sc_cast hp)] at hlt
            dsimp only [pa, Params4DT.C_R]
            have : (pa - (C_n : ℝ) / D_x - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
                (pa_n : ℝ) * D_x - ((D_p : ℝ) * C_n + (D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a)) := by
              dsimp only [pa]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
            nlinarith [mul_pos hDp hDx]
          dsimp only [cut3SumR]
          have hnn0 : (0 : ℝ) ≤ ((n0b - n0a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
          have hnn1 : (0 : ℝ) ≤ ((n1b - n1a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
          have hnn2 : (0 : ℝ) ≤ 2 * (((n2b - n2a : ℕ) : ℝ) / D_x) := mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))
          rw [max_eq_left hneg, max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
              max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
          ring
      rw [hR1, ← cut3Num_eq hp, hR2_le]
      set c1 := cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - B_sc - s_min_n)
      set c2 := cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pa_sc - C_sc - s_min_n)
      have hc2_le_c1 : c2 ≤ c1 := by
        have hv_nn : 0 ≤ (c1 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) - (c2 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) := by
          -- From integral of Pslab indicator ≥ 0!
          have hpaC_le_pbB : pa - C_R ≤ pb - B_R := by linarith [(hBC_lt hp)]
          have hle_i : ∫ y in C, ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - C_R}).indicator (fun _ => (1 : ℝ)) y ≤
              ∫ y in C, ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - B_R}).indicator (fun _ => (1 : ℝ)) y := by
            refine setIntegral_mono_on hi_lo hi_hi hCmeas (fun y _ => ?_)
            simp only [Set.indicator, mem_ofPred_eq]; split_ifs with h' h'' <;> try norm_num
            exfalso; exact h'' (le_trans h' hpaC_le_pbB)
          rw [vol_cut_box3_eq h0le_r h1le_r h2le_r, vol_cut_box3_eq h0le_r h1le_r h2le_r,
              hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le, hR1, ← cut3Num_eq hp, hR2_le] at hle_i
          linarith
        have : (c2 : ℝ) ≤ c1 := by
          have hpos : (0 : ℝ) < 12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3 := by positivity
          have := mul_nonneg hv_nn (le_of_lt hpos)
          have hring : ((c1 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) - (c2 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3)) *
              (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) = (c1 : ℝ) - c2 := by field_simp [ne_of_gt hDp, ne_of_gt hDx]
          linarith
        exact_mod_cast this
      have hden_nat : 0 < 12 * D_p2 * n0a * n1a * n2a * n2a * denom_sc :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (hDp2_nat_pos hp)) h0p) h1p) h2p) h2p) hdenom_pos
      have hcd : ((S_3 * D_x2 * (c1 - c2) : ℕ) : ℝ) ≤
          ((12 * D_p2 * n0a * n1a * n2a * n2a * denom_sc : ℕ) : ℝ) *
          (ceilDiv (S_3 * D_x2 * (c1 - c2)) (12 * D_p2 * n0a * n1a * n2a * n2a * denom_sc) : ℝ) := by
        exact_mod_cast le_mul_ceilDiv hden_nat
      rw [le_div_iff₀ (hS3_pos hp)]
      have hLHS : gain_c * ((c1 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) - (c2 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3)) * S_3 =
          ((S_3 * D_x2 * (c1 - c2) : ℕ) : ℝ) / ((12 * D_p2 * n0a * n1a * n2a * n2a * denom_sc : ℕ) : ℝ) := by
        dsimp only [gain_c]; simp only [Nat.cast_mul, (D_x2_cast hp), (D_p2_cast hp)]; rw [Nat.cast_sub hc2_le_c1]
        have h0r : (0 : ℝ) < n0a := Nat.cast_pos.mpr h0p
        have h1r : (0 : ℝ) < n1a := Nat.cast_pos.mpr h1p
        have h2r : (0 : ℝ) < n2a := Nat.cast_pos.mpr h2p
        have hdr : (0 : ℝ) < denom_sc := Nat.cast_pos.mpr hdenom_pos
        have hgen : ∀ (x0 x1 x2 d Dx Dp v1 v2 S3 : ℝ), Dx ≠ 0 → Dp ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → d ≠ 0 →
            1 / (x0 / Dx * (x1 / Dx) * (x2 / Dx) ^ 2 * (d / (Dp * Dx))) *
              (v1 / (12 * Dp ^ 3 * Dx ^ 3) - v2 / (12 * Dp ^ 3 * Dx ^ 3)) * S3 =
            (S3 * Dx ^ 2 * (v1 - v2)) / (12 * Dp ^ 2 * x0 * x1 * x2 * x2 * d) := by
          intro x0 x1 x2 d Dx Dp v1 v2 S3 h1 h2 h3 h4 h5 h6; field_simp [h1, h2, h3, h4, h5, h6]; try ring
        exact hgen n0a n1a n2a denom_sc D_x D_p c1 c2 S_3 (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt hdr)
      rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith
    · suffices hgoal : ∫ _ in C, gain_c ≤
          (ceilDiv (S_3 * D_x2 * D_p * (n0b - n0a) * (n1b - n1a) * (n2b - n2a))
            (facDen knd * n0a * n1a * n2a * n2a * denom_sc) : ℝ) / S_3 by
        cases knd with
        | box => exact absurd rfl hk
        | tri01 => exact hgoal
        | tri12 => exact hgoal
        | simp => exact hgoal
      -- Constant gain_c integrated over cell3Set knd = vol(cell3Set knd) * gain_c!
      have hvol_eq : ∫ _ in C, gain_c =
          (((n0b - n0a : ℕ) : ℝ) / D_x) * (((n1b - n1a : ℕ) : ℝ) / D_x) * (((n2b - n2a : ℕ) : ℝ) / D_x) / (facDen knd : ℝ) * gain_c := by
        -- Use hh_cell3 + jensen_cell3 on constant function!
        have h1 := hh_cell3 knd hok (convexOn_const gain_c (cell3Set_convex knd _ _ _ _ _ _)) continuousOn_const
        have h2 := jensen_cell3 knd hok (convexOn_const gain_c (cell3Set_convex knd _ _ _ _ _ _)) continuousOn_const
        have hsum_c : sumVerts3R (fun _ => gain_c) knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) =
            (nVerts3 knd : ℝ) * gain_c := by cases knd <;> simp [sumVerts3R, nVerts3] <;> ring
        rw [hsum_c] at h1
        have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
        rw [hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le] at h1 h2
        have hnv_ne : (nVerts3 knd : ℝ) ≠ 0 := by cases knd <;> simp [nVerts3]
        have h1' : ∫ _ in C, gain_c ≤
            (((n0b - n0a : ℕ) : ℝ) / D_x) * (((n1b - n1a : ℕ) : ℝ) / D_x) * (((n2b - n2a : ℕ) : ℝ) / D_x) / (facDen knd : ℝ) * gain_c := by
          refine le_trans h1 (le_of_eq ?_); field_simp [hnv_ne]
        exact le_antisymm h1' h2
      rw [hvol_eq]
      have hden_nat : 0 < facDen knd * n0a * n1a * n2a * n2a * denom_sc :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by cases knd <;> simp [facDen]) h0p) h1p) h2p) h2p) hdenom_pos
      have hcd : ((S_3 * D_x2 * D_p * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) : ℕ) : ℝ) ≤
          ((facDen knd * n0a * n1a * n2a * n2a * denom_sc : ℕ) : ℝ) *
          (ceilDiv (S_3 * D_x2 * D_p * (n0b - n0a) * (n1b - n1a) * (n2b - n2a))
            (facDen knd * n0a * n1a * n2a * n2a * denom_sc) : ℝ) := by
        exact_mod_cast le_mul_ceilDiv hden_nat
      have hfd_pos : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
      rw [le_div_iff₀ (hS3_pos hp)]
      have hLHS : (((n0b - n0a : ℕ) : ℝ) / D_x) * (((n1b - n1a : ℕ) : ℝ) / D_x) * (((n2b - n2a : ℕ) : ℝ) / D_x) / (facDen knd : ℝ) * gain_c * S_3 =
          ((S_3 * D_x2 * D_p * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) : ℕ) : ℝ) /
          ((facDen knd * n0a * n1a * n2a * n2a * denom_sc : ℕ) : ℝ) := by
        dsimp only [gain_c]; simp only [Nat.cast_mul, (D_x2_cast hp)]
        have h0r : (0 : ℝ) < n0a := Nat.cast_pos.mpr h0p
        have h1r : (0 : ℝ) < n1a := Nat.cast_pos.mpr h1p
        have h2r : (0 : ℝ) < n2a := Nat.cast_pos.mpr h2p
        have hdr : (0 : ℝ) < denom_sc := Nat.cast_pos.mpr hdenom_pos
        have hgen : ∀ (dx0 dx1 dx2 x0 x1 x2 d Dx Dp fd S3 : ℝ), Dx ≠ 0 → Dp ≠ 0 → fd ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → d ≠ 0 →
            dx0 / Dx * (dx1 / Dx) * (dx2 / Dx) / fd *
              (1 / (x0 / Dx * (x1 / Dx) * (x2 / Dx) ^ 2 * (d / (Dp * Dx)))) * S3 =
            (S3 * Dx ^ 2 * Dp * dx0 * dx1 * dx2) / (fd * x0 * x1 * x2 * x2 * d) := by
          intro dx0 dx1 dx2 x0 x1 x2 d Dx Dp fd S3 h1 h2 h3 h4 h5 h6 h7; field_simp [h1, h2, h3, h4, h5, h6, h7]; try ring
        exact hgen (n0b - n0a : ℕ) (n1b - n1a : ℕ) (n2b - n2a : ℕ) n0a n1a n2a denom_sc D_x D_p (facDen knd) S_3 (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt hfd_pos) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt hdr)
      rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith


private lemma cell3_Mp_neg_bound {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ((evalMpLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b).2 : ℝ) / S_3 ≤
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      mpDropFn p pa_n pb_n n0b n1b n2b y := by
  have hv' := hv
  have hdrop_cont : ContinuousOn (mpDropFn p pa_n pb_n n0b n1b n2b)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :=
    mpDropFn_continuousOn hp hpa_le h12 hpb_ge hv'
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab : Set (Fin 3 → ℝ) := {y | pa - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pb - B_R}
  set denom_sc := max B_sc (pa_sc - s_max_n)
  have hdenom_pos : 0 < denom_sc := lt_of_lt_of_le ((hBsc_nat_pos hp)) (le_max_left _ _)
  let gain_c : ℝ := 1 / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((denom_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  set m_lo_sc := max B_sc (min C_sc (pa_sc - s_max_n))
  let m_lo_r : ℝ := (m_lo_sc : ℝ) / ((D_p : ℝ) * D_x)
  let xm_r : ℝ := (B_R + m_lo_r) / 2
  let drop_fn : (Fin 3 → ℝ) → ℝ := mpDropFn p pa_n pb_n n0b n1b n2b
  have hm_lo_props : B_sc < m_lo_sc → B_R < m_lo_r ∧ m_lo_r ≤ C_R ∧ (∀ y ∈ C, m_lo_r ≤ φ1 - y 0 - y 1 - 2 * y 2) :=
    mp_m_lo_props hp hpa_le hv'
  dsimp only [Buchstab4DT.evalMpLeaf]
  have hneg_bnd :
      ((if m_lo_sc ≤ B_sc then 0
        else
          let (c0, c1, c2) :=
            match knd with
            | .box => (6 * (n0a + n0b), 6 * (n1a + n1b), 6 * (n2a + n2b))
            | .tri01 => (4 * (2 * n0a + n0b), 4 * (n0a + 2 * n0b), 6 * (n2a + n2b))
            | .tri12 => (6 * (n0a + n0b), 4 * (2 * n1a + n1b), 4 * (n1a + 2 * n1b))
            | .simp => (3 * (3 * n0a + n0b), 6 * (n0a + n0b), 3 * (n0a + 3 * n0b))
          let xm2_sc := B_sc + m_lo_sc
          let rem12_sc := 12 * pb_sc - D_p * (c0 + c1 + c2) - 6 * xm2_sc
          (S_3 * 497664 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (m_lo_sc - B_sc)) /
            (facDen knd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc) : ℕ) : ℝ) / S_3 ≤
      ∫ y in C, drop_fn y := by
    by_cases hmlo_z : m_lo_sc ≤ B_sc
    · dsimp only [drop_fn, mpDropFn]; rw [if_pos hmlo_z, if_pos hmlo_z]; simp
    · push Not at hmlo_z
      dsimp only [drop_fn, mpDropFn]; rw [if_neg (not_le.mpr hmlo_z), if_neg (not_le.mpr hmlo_z)]
      rcases hm_lo_props hmlo_z with ⟨hB_lt_m, _, hm_le_cut⟩
      -- Apply jensen_cell3 to drop_fn (jointly convex on C!)
      have hconv_d : ConvexOn ℝ C (fun y => (m_lo_r - B_R) / (y 0 * y 1 * y 2 * xm_r * (pb - (y 0 + y 1 + y 2) - xm_r) ^ 2)) := by
        let L : Fin 5 → (Fin 3 → ℝ) → ℝ :=
          ![fun y => y 0, fun y => y 1, fun y => y 2, fun y => pb - (y 0 + y 1 + y 2) - xm_r, fun y => pb - (y 0 + y 1 + y 2) - xm_r]
        have hfeq : (fun y : Fin 3 → ℝ => (m_lo_r - B_R) / (y 0 * y 1 * y 2 * xm_r * (pb - (y 0 + y 1 + y 2) - xm_r) ^ 2)) =
            fun y => ((m_lo_r - B_R) / xm_r) • (∏ i : Fin 5, L i y)⁻¹ := by
          ext y; dsimp only [L]; rw [Fin.prod_univ_five, smul_eq_mul, sq]; simp [div_eq_mul_inv]; ring
        rw [hfeq]
        have hcv := convexOn_inv_prod (cell3Set_convex knd _ _ _ _ _ _) L
          (fun i _ _ _ _ a b _ _ hab => by have ha1 : a = 1 - b := (by linarith only [hab]); fin_cases i <;> simp [L, smul_eq_mul] <;> (rw [ha1]; ring))
          (fun i y hy => by
            rcases hmem_simp y hy with ⟨h0, h1, h2⟩
            fin_cases i <;> dsimp only [L]
            · exact lt_of_lt_of_le (hA_pos hp) h0.1
            · exact lt_of_lt_of_le (hA_pos hp) h1.1
            · exact lt_of_lt_of_le (hA_pos hp) h2.1
            · change 0 < pb - (y 0 + y 1 + y 2) - xm_r; dsimp only [xm_r]; linarith [hm_le_cut y hy, h12, hpb_ge, hB_lt_m, lt_of_lt_of_le (hA_pos hp) h2.1]
            · change 0 < pb - (y 0 + y 1 + y 2) - xm_r; dsimp only [xm_r]; linarith [hm_le_cut y hy, h12, hpb_ge, hB_lt_m, lt_of_lt_of_le (hA_pos hp) h2.1])
        exact hcv.smul (div_nonneg (sub_nonneg.mpr (le_of_lt hB_lt_m)) (by dsimp only [xm_r]; linarith))
      have hj3 := jensen_cell3 knd hok hconv_d (by dsimp only [drop_fn, mpDropFn] at hdrop_cont; rwa [if_neg (not_le.mpr hmlo_z)] at hdrop_cont)
      refine le_trans ?_ hj3
      -- Match centroid3R with (c0, c1, c2) / (12 * D_x) and apply Nat.div_mul_le_self!
      set c_t := match knd with
        | .box => (6 * (n0a + n0b), 6 * (n1a + n1b), 6 * (n2a + n2b))
        | .tri01 => (4 * (2 * n0a + n0b), 4 * (n0a + 2 * n0b), 6 * (n2a + n2b))
        | .tri12 => (6 * (n0a + n0b), 4 * (2 * n1a + n1b), 4 * (n1a + 2 * n1b))
        | .simp => (3 * (3 * n0a + n0b), 6 * (n0a + n0b), 3 * (n0a + 3 * n0b))
      set c0 := c_t.1; set c1 := c_t.2.1; set c2 := c_t.2.2
      have hcent_eq : centroid3R knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) =
          ![(c0 : ℝ) / (12 * D_x), (c1 : ℝ) / (12 * D_x), (c2 : ℝ) / (12 * D_x)] := by
        cases knd <;> (ext i; fin_cases i <;> simp [centroid3R, c0, c1, c2, c_t] <;> ring)
      rw [hcent_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hc0p : 0 < c0 := by cases knd <;> dsimp only [c0, c_t] <;> omega
      have hc1p : 0 < c1 := by cases knd <;> dsimp only [c1, c_t] <;> omega
      have hc2p : 0 < c2 := by cases knd <;> dsimp only [c2, c_t] <;> omega
      have hcent_in : ![(c0 : ℝ) / (12 * D_x), (c1 : ℝ) / (12 * D_x), (c2 : ℝ) / (12 * D_x)] ∈ C := by
        rw [← hcent_eq]
        cases knd with
        | box =>
          dsimp only [C, cell3Set, centroid3R, mem_ofPred_eq, mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          exact ⟨⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.2.1], by linarith [hok.2.1]⟩, ⟨by linarith [hok.2.2.1], by linarith [hok.2.2.1]⟩⟩
        | tri01 =>
          rcases ht01 rfl with ⟨rfl, rfl⟩
          dsimp only [C, cell3Set, centroid3R, mem_ofPred_eq, mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          exact ⟨⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.2.2.1], by linarith [hok.2.2.1]⟩, by linarith [hok.1]⟩
        | tri12 =>
          rcases ht12 rfl with ⟨rfl, rfl⟩
          dsimp only [C, cell3Set, centroid3R, mem_ofPred_eq, mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          exact ⟨⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.2.1], by linarith [hok.2.1]⟩, ⟨by linarith [hok.2.1], by linarith [hok.2.1]⟩, by linarith [hok.2.1]⟩
        | simp =>
          rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩
          dsimp only [C, cell3Set, centroid3R, mem_ofPred_eq, mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          exact ⟨⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.1], by linarith [hok.1]⟩, ⟨by linarith [hok.1], by linarith [hok.1]⟩, by linarith [hok.1], by linarith [hok.1]⟩
      have hrem_pos_r : 0 < pb - ((c0 : ℝ) / (12 * D_x) + (c1 : ℝ) / (12 * D_x) + (c2 : ℝ) / (12 * D_x)) - xm_r := by
        have hcut := hm_le_cut _ hcent_in
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hcut
        have hc2_pos : (0 : ℝ) < (c2 : ℝ) / (12 * D_x) := div_pos (by exact_mod_cast hc2p) (by positivity)
        dsimp only [xm_r]; linarith [h12, hpb_ge]
      set xm2_sc := B_sc + m_lo_sc
      have hxm_eq : xm_r = (xm2_sc : ℝ) / (2 * (D_p : ℝ) * D_x) := by
        dsimp only [xm_r, xm2_sc, Params4DT.B_R, m_lo_r]; rw [Nat.cast_add, (B_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      have hrem_nat_pos : D_p * (c0 + c1 + c2) + 6 * xm2_sc < 12 * pb_sc := by
        have h1 : (0 : ℝ) < (pb - ((c0 : ℝ) / (12 * D_x) + (c1 : ℝ) / (12 * D_x) + (c2 : ℝ) / (12 * D_x)) - xm_r) * (12 * (D_p : ℝ) * D_x) :=
          mul_pos hrem_pos_r (by positivity)
        have h2 : (pb - ((c0 : ℝ) / (12 * D_x) + (c1 : ℝ) / (12 * D_x) + (c2 : ℝ) / (12 * D_x)) - xm_r) * (12 * (D_p : ℝ) * D_x) =
            ((12 * pb_sc : ℕ) : ℝ) - ((D_p * (c0 + c1 + c2) + 6 * xm2_sc : ℕ) : ℝ) := by
          rw [hxm_eq]; dsimp only [pb, pb_sc]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        have h3 : ((D_p * (c0 + c1 + c2) + 6 * xm2_sc : ℕ) : ℝ) < ((12 * pb_sc : ℕ) : ℝ) := by linarith
        exact_mod_cast h3
      set rem12_sc := 12 * pb_sc - D_p * (c0 + c1 + c2) - 6 * xm2_sc
      have hrem12_pos : 0 < rem12_sc := by dsimp only [rem12_sc]; omega
      have hrem_eq : pb - ((c0 : ℝ) / (12 * D_x) + (c1 : ℝ) / (12 * D_x) + (c2 : ℝ) / (12 * D_x)) - xm_r =
          (rem12_sc : ℝ) / (12 * (D_p : ℝ) * D_x) := by
        dsimp only [rem12_sc]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hxm_eq]
        dsimp only [pb, pb_sc]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      have hxm2_pos : 0 < xm2_sc := Nat.add_pos_left ((hBsc_nat_pos hp)) _
      have hden_nat : 0 < facDen knd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by cases knd <;> simp [facDen]) hc0p) hc1p) hc2p) hxm2_pos) hrem12_pos) hrem12_pos
      have hfl : ((S_3 * 497664 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (m_lo_sc - B_sc) /
          (facDen knd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc) : ℕ) : ℝ) *
          ((facDen knd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc : ℕ) : ℝ) ≤
          ((S_3 * 497664 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (m_lo_sc - B_sc) : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self _ _
      have hRHS_eq : ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
          ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) / (facDen knd : ℝ) *
          ((m_lo_r - B_R) / ((c0 : ℝ) / (12 * D_x) * ((c1 : ℝ) / (12 * D_x)) * ((c2 : ℝ) / (12 * D_x)) * xm_r *
            (pb - ((c0 : ℝ) / (12 * D_x) + (c1 : ℝ) / (12 * D_x) + (c2 : ℝ) / (12 * D_x)) - xm_r) ^ 2)) =
          ((S_3 * 497664 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (m_lo_sc - B_sc) : ℕ) : ℝ) /
          (((facDen knd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc : ℕ) : ℝ) * S_3) := by
        rw [hrem_eq, hxm_eq]
        have hmlo_sub : m_lo_r - B_R = ((m_lo_sc - B_sc : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
          rw [Nat.cast_sub (le_of_lt hmlo_z)]; dsimp only [m_lo_r, Params4DT.B_R]; rw [(B_sc_cast hp)]
          field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        rw [hmlo_sub]
        simp only [Nat.cast_mul, (D_x2_cast hp), (D_p2_cast hp)]
        rw [Nat.cast_sub h0le, Nat.cast_sub h1le, Nat.cast_sub h2le]
        have hfd_p : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
        have hc0r : (0 : ℝ) < c0 := Nat.cast_pos.mpr hc0p
        have hc1r : (0 : ℝ) < c1 := Nat.cast_pos.mpr hc1p
        have hc2r : (0 : ℝ) < c2 := Nat.cast_pos.mpr hc2p
        have hxm2r : (0 : ℝ) < xm2_sc := Nat.cast_pos.mpr (show 0 < xm2_sc by dsimp only [xm2_sc]; exact Nat.add_pos_left ((hBsc_nat_pos hp)) _)
        have hremr : (0 : ℝ) < rem12_sc := Nat.cast_pos.mpr hrem12_pos
        have hgen : ∀ (a0 b0 a1 b1 a2 b2 c0 c1 c2 dm xm rem Dx Dp fd S3 : ℝ),
            Dx ≠ 0 → Dp ≠ 0 → S3 ≠ 0 → fd ≠ 0 → c0 ≠ 0 → c1 ≠ 0 → c2 ≠ 0 → xm ≠ 0 → rem ≠ 0 →
            (b0 / Dx - a0 / Dx) * (b1 / Dx - a1 / Dx) * (b2 / Dx - a2 / Dx) / fd *
              (dm / (Dp * Dx) / (c0 / (12 * Dx) * (c1 / (12 * Dx)) * (c2 / (12 * Dx)) * (xm / (2 * Dp * Dx)) * (rem / (12 * Dp * Dx)) ^ 2)) =
            (S3 * 497664 * Dx ^ 2 * Dp ^ 2 * (b0 - a0) * (b1 - a1) * (b2 - a2) * dm) /
              (fd * c0 * c1 * c2 * xm * rem * rem * S3) := by
          intro a0 b0 a1 b1 a2 b2 c0 c1 c2 dm xm rem Dx Dp fd S3 h1 h2 h3 h4 h5 h6 h7 h8 h9
          have hsub : ∀ u v : ℝ, v / Dx - u / Dx = (v - u) / Dx := fun u v => (sub_div v u Dx).symm
          rw [hsub a0 b0, hsub a1 b1, hsub a2 b2]
          field_simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]; try ring
        exact hgen n0a n0b n1a n1b n2a n2b c0 c1 c2 (m_lo_sc - B_sc : ℕ) xm2_sc rem12_sc D_x D_p (facDen knd) S_3
          (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt (hS3_pos hp)) (ne_of_gt hfd_p) (ne_of_gt hc0r) (ne_of_gt hc1r) (ne_of_gt hc2r) (ne_of_gt hxm2r) (ne_of_gt hremr)
      rw [hRHS_eq, div_le_div_iff₀ (hS3_pos hp) (mul_pos (by exact_mod_cast hden_nat) (hS3_pos hp)), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfl (le_of_lt (hS3_pos hp))
  exact hneg_bnd

private lemma cell3_Mp_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    let r := evalMpLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1) ≤
      ((r.1 : ℝ) - (r.2 : ℝ)) / S_3 := by
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hgain_int : IntegrableOn (mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b) C volume := by
    unfold mpGainFn; dsimp only; split_ifs
    · exact continuousOn_const.integrableOn_compact (cell3Set_isCompact knd _ _ _ _ _ _)
    · cases knd with
      | box =>
        have hPslab_m : MeasurableSet {y : Fin 3 → ℝ | (pa_n : ℝ) / D_p - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ (pb_n : ℝ) / D_p - B_R} :=
          show MeasurableSet ({y : Fin 3 → ℝ | (pa_n : ℝ) / D_p - C_R < y 0 + y 1 + 2 * y 2} ∩ {y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ (pb_n : ℝ) / D_p - B_R}) from
            (isOpen_lt continuous_const (by fun_prop : Continuous fun y : Fin 3 → ℝ => y 0 + y 1 + 2 * y 2)).measurableSet.inter
              (isClosed_le (by fun_prop : Continuous fun y : Fin 3 → ℝ => y 0 + y 1 + 2 * y 2) continuous_const).measurableSet
        exact (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator hPslab_m
      | _ => exact continuousOn_const.integrableOn_compact (cell3Set_isCompact _ _ _ _ _ _ _)
  have hdrop_int : IntegrableOn (mpDropFn p pa_n pb_n n0b n1b n2b) C volume :=
    (mpDropFn_continuousOn hp hpa_le h12 hpb_ge hv).integrableOn_compact (cell3Set_isCompact knd _ _ _ _ _ _)
  have hG_int : IntegrableOn (fun y => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1)) C volume := by
    have h1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) hv
    have h2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) hv
    have heq : (fun y : Fin 3 → ℝ => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1)) =
        fun y => ((1 / (y 0 * y 1 * y 2)) * G_fn φ2 y - (1 / (y 0 * y 1 * y 2)) * G_fn φ1 y) / (φ2 - φ1) := by ext y; ring
    rw [heq]; exact (h2.sub h1).div_const _
  have hint_le : ∫ y in C, ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1) ≤
      (∫ y in C, mpGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y) - (∫ y in C, mpDropFn p pa_n pb_n n0b n1b n2b y) := by
    rw [← integral_sub hgain_int hdrop_int]
    exact setIntegral_mono_on hG_int (hgain_int.sub hdrop_int) hCmeas (cell3_Mp_pt hp hpa_le h12 hpb_ge hv)
  have hpos := cell3_Mp_pos_bound hp hpa_le h12 hpb_ge hv
  have hneg := cell3_Mp_neg_bound hp hpa_le h12 hpb_ge hv
  dsimp only; rw [sub_div]; linarith only [hint_le, hpos, hneg]

private lemma mmDropFn_continuousOn {pa_n pb_n : ℕ}
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ContinuousOn (mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  rcases hv with ⟨hA0, _, h0B, hA1, _, h1B, hA2, _, h2B, ht01, ht12, hts⟩
  unfold mmDropFn; dsimp only; split_ifs with h1 h2
  · exact continuousOn_const
  · have hpa_ge : (n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R ≤ (pa_n : ℝ) / D_p := by
      have h' : ((D_p * (n0b + n1b + 2 * n2b) + C_sc : ℕ) : ℝ) ≤ ((pa_n * D_x : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast [(C_sc_cast hp)] at h'
      have : ((pa_n : ℝ) / D_p - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R)) * ((D_p : ℝ) * D_x) =
          (pa_n : ℝ) * D_x - ((D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * C_n) := by
        dsimp only [Params4DT.C_R]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      nlinarith [mul_pos hDp hDx]
    have hmem : ∀ y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
        y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧ y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧ y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
      intro y hy; cases knd with
      | box => exact hy
      | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
      | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · refine continuousOn_const.div (by fun_prop) (fun y hy => ?_)
      rcases hmem y hy with ⟨hy0, hy1, hy2⟩
      have : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) hy0.1)
      have : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) hy1.1)
      have : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) hy2.1)
      have : 0 < (pa_n : ℝ) / D_p - (y 0 + y 1 + y 2) - B_R := by linarith [hy0.2, hy1.2, hy2.2, (hBC_lt hp)]
      positivity
    · refine continuousOn_const.div (by fun_prop) (fun y hy => ?_)
      rcases hmem y hy with ⟨hy0, hy1, hy2⟩
      have : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) hy0.1)
      have : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) hy1.1)
      have : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) hy2.1)
      have : 0 < (pa_n : ℝ) / D_p - (y 0 + y 1 + y 2) - C_R := by linarith [hy0.2, hy1.2, hy2.2]
      positivity
  · exact (Continuous.continuousOn (by fun_prop)).div_const _

private lemma cell3_Mm_pt_drop {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    {y : Fin 3 → ℝ}
    (hy : y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :
    (1 / (y 0 * y 1 * y 2)) *
      (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) ≤
      mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b y := by
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab_in : Set (Fin 3 → ℝ) := {y | pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R}
  set denom_x3_sc := min C_sc (pb_sc - s_min_n)
  set denom_x2_sc := D_p * n2b + (pb_sc - pa_sc)
  let drop_fn : (Fin 3 → ℝ) → ℝ := mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b
  let gain_c : ℝ := 1 / (((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) *
    ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
  have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
  have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
  have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
  rcases hmem y hy with ⟨hy0, hy1, hy2⟩
  rcases hmem_simp y hy with ⟨hA0y, hA1y, hA2y⟩
  have hy0p : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hA0y.1
  have hy1p : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hA1y.1
  have hy2p : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hA2y.1
  set m1 := max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))
  set m2 := max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))
  have hBm1 : B_R ≤ m1 := le_max_left _ _
  have hm12 : m1 ≤ m2 := max_le_max_left B_R (min_le_min_left C_R (by linarith))
  have hBm2 : B_R ≤ m2 := le_trans hBm1 hm12
  -- Part A: drop_ub
  have hdrop_ub : (1 / (y 0 * y 1 * y 2)) *
      (∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) ≤ drop_fn y := by
    dsimp only [drop_fn, mmDropFn]
    split_ifs with hz_pb hint_case
    · have hle_r : pb ≤ (n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + B_R := by
        have h' : (pb_sc : ℝ) ≤ ((s_min_n + B_sc : ℕ) : ℝ) := by exact_mod_cast hz_pb
        dsimp only [pb_sc, s_min_n] at h'; push_cast [(B_sc_cast hp)] at h'
        dsimp only [pb, Params4DT.B_R]
        have : (pb - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + (B_n : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
            (pb_n : ℝ) * D_x - ((D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a) + (D_p : ℝ) * B_n) := by
          dsimp only [pb]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        nlinarith [mul_pos hDp hDx]
      have hm1B : m1 = B_R := max_eq_left (le_trans (min_le_right _ _) (by linarith [hy0.1, hy1.1, hy2.1]))
      rw [hm1B, intervalIntegral.integral_same, mul_zero]
    · -- Interior case: s_max_n + C_sc ≤ pa_sc -> m1 = C_R! Use hh1_Icc (trapezoid rule)!
      have hpa_ge : (n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R ≤ pa := by
        have h' : ((s_max_n + C_sc : ℕ) : ℝ) ≤ (pa_sc : ℝ) := by exact_mod_cast hint_case
        dsimp only [s_max_n, pa_sc] at h'; push_cast [(C_sc_cast hp)] at h'
        dsimp only [pa, Params4DT.C_R]
        have : (pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + (C_n : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
            (pa_n : ℝ) * D_x - ((D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * C_n) := by
          dsimp only [pa]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        nlinarith [mul_pos hDp hDx]
      have hm1C : m1 = C_R := by
        dsimp only [m1]; rw [min_eq_left (by linarith [hy0.2, hy1.2, hy2.2]), max_eq_right (le_of_lt (hBC_lt hp))]
      rw [hm1C]
      have hc_l : ContinuousOn (fun x3 => 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc B_R C_R) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
          have : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hy0.2, hy1.2, hy2.2]
          have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith

          positivity)
      have hc_r : ContinuousOn (fun x3 => 1 / (x3 * (pa - (y 0 + y 1 + y 2) - x3) ^ 2)) (Icc B_R C_R) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
          have : 0 < pa - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hy0.2, hy1.2, hy2.2]

          positivity)
      have hconv_r : ConvexOn ℝ (Icc B_R C_R) (fun x3 => 1 / (x3 * (pa - (y 0 + y 1 + y 2) - x3) ^ 2)) := by
        let L : Fin 3 → ℝ → ℝ := ![fun t => t, fun t => pa - (y 0 + y 1 + y 2) - t, fun t => pa - (y 0 + y 1 + y 2) - t]
        have hfeq : (fun x3 : ℝ => 1 / (x3 * (pa - (y 0 + y 1 + y 2) - x3) ^ 2)) = fun t => (∏ i : Fin 3, L i t)⁻¹ := by
          ext t; dsimp only [L]; rw [Fin.prod_univ_three, one_div, sq]; simp; ring
        rw [hfeq]
        refine convexOn_inv_prod (convex_Icc B_R C_R) L
          (fun i _ _ _ _ a b _ _ hab => by have ha1 : a = 1 - b := (by linarith only [hab]); fin_cases i <;> simp [L, smul_eq_mul] <;> (rw [ha1]; ring)) ?_
        intro i t ht; fin_cases i <;> dsimp only [L]
        · exact lt_of_lt_of_le hBpos ht.1
        · change 0 < pa - (y 0 + y 1 + y 2) - t; linarith [ht.2, hy0.2, hy1.2, hy2.2]
        · change 0 < pa - (y 0 + y 1 + y 2) - t; linarith [ht.2, hy0.2, hy1.2, hy2.2]
      have hmono : ∫ x3 in B_R..C_R, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) ≤
          ∫ x3 in B_R..C_R, 1 / (x3 * (pa - (y 0 + y 1 + y 2) - x3) ^ 2) := by
        apply intervalIntegral.integral_mono_on (le_of_lt (hBC_lt hp)) (hc_l.intervalIntegrable_of_Icc (le_of_lt (hBC_lt hp)))
          (hc_r.intervalIntegrable_of_Icc (le_of_lt (hBC_lt hp)))
        intro x3 hx3
        have hx3p : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
        have hrp : 0 < pa - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hy0.2, hy1.2, hy2.2]
        have hle_den : x3 * (pa - (y 0 + y 1 + y 2) - x3) ^ 2 ≤
            x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3) := by
          rw [sq, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (by linarith) (le_of_lt hrp) (by linarith)) (le_of_lt hx3p)
        exact div_le_div₀ (by norm_num) (le_refl 1) (by positivity) hle_den
      have hhh := hh1_Icc (le_of_lt (hBC_lt hp)) hconv_r hc_r
      have hmul := mul_le_mul_of_nonneg_left (le_trans hmono hhh) (show (0 : ℝ) ≤ 1 / (y 0 * y 1 * y 2) by positivity)
      refine le_trans hmul (le_of_eq ?_)
      simp only [div_eq_mul_inv, mul_inv]; ring
    · -- Slab case: bound integrand by 1/(B_R * y2^2) on [B_R, m1], and m1 - B_R ≤ min(C_R - B_R, (pb - B_R - y0 - y1 - 2*y2)_+)!
      have hm1_sub : m1 - B_R ≤ max 0 (pb - B_R - (y 0 + y 1 + 2 * y 2)) - max 0 (pb - C_R - (y 0 + y 1 + 2 * y 2)) := by
        have h1 : m1 - B_R ≤ C_R - B_R := by linarith [max_le (le_of_lt (hBC_lt hp)) (min_le_left C_R (φ1 - y 0 - y 1 - 2 * y 2))]
        have h2 : m1 - B_R ≤ max 0 (pb - B_R - (y 0 + y 1 + 2 * y 2)) := by
          by_cases h : φ1 - y 0 - y 1 - 2 * y 2 ≤ B_R
          · have : m1 = B_R := max_eq_left (le_trans (min_le_right _ _) h)
            rw [this, sub_self]; exact le_max_left 0 _
          · push Not at h
            have : m1 ≤ pb - y 0 - y 1 - 2 * y 2 := max_le (by linarith) (le_trans (min_le_right _ _) (by linarith))
            exact le_trans (by linarith) (le_max_right 0 _)
        by_cases hC : pb - C_R - (y 0 + y 1 + 2 * y 2) ≤ 0
        · rw [max_eq_left hC, sub_zero]; exact h2
        · push Not at hC
          rw [max_eq_right (le_of_lt hC), max_eq_right (by linarith only [(hBC_lt hp), hC])]
          linarith only [h1]
      by_cases hm1B : m1 = B_R
      · rw [hm1B, intervalIntegral.integral_same, mul_zero]
        have hnn : 0 ≤ max 0 (pb - B_R - (y 0 + y 1 + 2 * y 2)) - max 0 (pb - C_R - (y 0 + y 1 + 2 * y 2)) :=
          sub_nonneg.mpr (max_le_max_left 0 (by linarith only [(hBC_lt hp)]))
        exact div_nonneg hnn (by positivity)
      · have hm1_le_cut : m1 ≤ φ1 - y 0 - y 1 - 2 * y 2 := by
          have : m1 = min C_R (φ1 - y 0 - y 1 - 2 * y 2) :=
            max_eq_right (by by_contra hlt; push Not at hlt; exact hm1B (max_eq_left (le_of_lt hlt)))
          rw [this]; exact min_le_right _ _
        have hc_l : ContinuousOn (fun x3 => 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc B_R m1) :=
          continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
            have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
            have hr1' : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith only [hx3.2, hm1_le_cut, hy2p]
            have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith only [h12, hr1']

            positivity)
        have hmono : ∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) ≤
            (m1 - B_R) * (1 / (B_R * y 2 ^ 2)) := by
          have h := intervalIntegral.integral_mono_on hBm1 (hc_l.intervalIntegrable_of_Icc hBm1)
            (intervalIntegrable_const : IntervalIntegrable (fun _ => 1 / (B_R * y 2 ^ 2)) volume B_R m1)
            (fun x3 hx3 => by
              have hr1 : y 2 ≤ φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm1_le_cut]
              have hr2 : y 2 ≤ φ2 - (y 0 + y 1 + y 2) - x3 := by linarith
              refine div_le_div₀ (by norm_num) (le_refl 1) (mul_pos hBpos (sq_pos_of_pos hy2p)) ?_
              rw [sq, mul_assoc x3]
              exact mul_le_mul hx3.1 (mul_le_mul hr1 hr2 (le_of_lt hy2p) (le_trans (le_of_lt hy2p) hr1)) (mul_nonneg (le_of_lt hy2p) (le_of_lt hy2p)) (le_trans (le_of_lt hBpos) hx3.1))
          rwa [intervalIntegral.integral_const, smul_eq_mul] at h
        have hstep1 : (1 / (y 0 * y 1 * y 2)) *
            (∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) ≤
            (m1 - B_R) / (y 0 * y 1 * y 2 ^ 3 * B_R) := by
          have hmul := mul_le_mul_of_nonneg_left hmono (show (0 : ℝ) ≤ 1 / (y 0 * y 1 * y 2) by positivity)
          refine le_trans hmul (le_of_eq ?_); field_simp [ne_of_gt hy0p, ne_of_gt hy1p, ne_of_gt hy2p, ne_of_gt hBpos]; try ring
        refine le_trans hstep1 ?_
        have h0a_p : (0 : ℝ) < (n0a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h0p) hDx
        have h1a_p : (0 : ℝ) < (n1a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h1p) hDx
        have h2a_p : (0 : ℝ) < (n2a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h2p) hDx
        have hden_le : ((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R ≤ y 0 * y 1 * y 2 ^ 3 * B_R := by
          have h01 := mul_le_mul hy0.1 hy1.1 (le_of_lt h1a_p) (le_trans (le_of_lt h0a_p) hy0.1)
          have h23 : ((n2a : ℝ) / D_x) ^ 3 ≤ y 2 ^ 3 := pow_le_pow_left₀ (le_of_lt h2a_p) hy2.1 3
          exact mul_le_mul_of_nonneg_right (mul_le_mul h01 h23 (by positivity) (by positivity)) (le_of_lt hBpos)
        exact div_le_div₀ (by linarith [sub_nonneg.mpr hBm1]) hm1_sub (by positivity) hden_le
  exact hdrop_ub

private lemma cell3_Mm_pt_gain {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    {y : Fin 3 → ℝ}
    (hy : y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :
    mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y ≤
      ((1 / (y 0 * y 1 * y 2)) *
        (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
          1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) := by
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab_in : Set (Fin 3 → ℝ) := {y | pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R}
  set denom_x3_sc := min C_sc (pb_sc - s_min_n)
  set denom_x2_sc := D_p * n2b + (pb_sc - pa_sc)
  let drop_fn : (Fin 3 → ℝ) → ℝ := mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b
  let gain_c : ℝ := 1 / (((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) *
    ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
  have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
  have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
  have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
  rcases hmem y hy with ⟨hy0, hy1, hy2⟩
  rcases hmem_simp y hy with ⟨hA0y, hA1y, hA2y⟩
  have hy0p : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hA0y.1
  have hy1p : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hA1y.1
  have hy2p : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hA2y.1
  set m1 := max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))
  set m2 := max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))
  have hBm1 : B_R ≤ m1 := le_max_left _ _
  have hm12 : m1 ≤ m2 := max_le_max_left B_R (min_le_min_left C_R (by linarith))
  have hBm2 : B_R ≤ m2 := le_trans hBm1 hm12
  -- Part B: gain_lb
  have hgain_lb : gain_fn y ≤ ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) := by
    have hnonneg_rhs : 0 ≤ ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) := by
      apply div_nonneg (mul_nonneg (by positivity) ?_) (le_of_lt h12pos)
      by_cases hm12_eq : m1 = m2
      · rw [hm12_eq, intervalIntegral.integral_same]
      · have hm2B : m2 ≠ B_R := fun h => hm12_eq ((le_antisymm (h ▸ hm12) hBm1).trans h.symm)
        have hm2_le_cut : m2 ≤ φ2 - y 0 - y 1 - 2 * y 2 := by
          have : m2 = min C_R (φ2 - y 0 - y 1 - 2 * y 2) :=
            max_eq_right (by by_contra hlt; push Not at hlt; exact hm2B (max_eq_left (le_of_lt hlt)))
          rw [this]; exact min_le_right _ _
        apply intervalIntegral.integral_nonneg hm12
        intro x3 hx3
        have : 0 < x3 := lt_of_lt_of_le (lt_of_lt_of_le hBpos hBm1) hx3.1
        have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm2_le_cut]

        positivity
    have hcore : pb - C_R ≤ y 0 + y 1 + 2 * y 2 → y 0 + y 1 + 2 * y 2 ≤ pa - B_R →
        ¬ (s_max_n + C_sc ≤ pb_sc ∨ pa_sc ≤ s_min_n + B_sc) →
        gain_c ≤ ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) := by
      intro hlb hub hnotz
      have hm1_eq : m1 = φ1 - y 0 - y 1 - 2 * y 2 := by
        dsimp only [m1]
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      have hm2_eq : m2 = φ2 - y 0 - y 1 - 2 * y 2 := by
        dsimp only [m2]
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      have hlen : m2 - m1 = φ2 - φ1 := by rw [hm1_eq, hm2_eq]; ring
      have hdx3_pos : 0 < (denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x) := by
        have hp : 0 < denom_x3_sc := by
          dsimp only [denom_x3_sc]
          have h1 : 0 < C_sc := (hCsc_nat_pos hp)
          have h2 : s_min_n < pb_sc := by
            have : s_min_n + B_sc < pa_sc := by push Not at hnotz; exact hnotz.2
            have : pa_sc ≤ pb_sc := by
              have : (pa_n : ℝ) ≤ pb_n := by
                have := mul_le_mul_of_nonneg_right (le_trans hpa_le (le_trans (le_of_lt h12) hpb_ge)) (le_of_lt hDp)
                have : pa * D_p = pa_n := div_mul_cancel₀ _ (ne_of_gt hDp)
                have : pb * D_p = pb_n := div_mul_cancel₀ _ (ne_of_gt hDp)
                linarith
              exact Nat.mul_le_mul_right D_x (by exact_mod_cast this)
            omega
          exact lt_min h1 (Nat.sub_pos_of_lt h2)
        exact div_pos (by exact_mod_cast hp) (mul_pos hDp hDx)
      have hdx2_pos : 0 < (denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x) := by
        have hp : 0 < denom_x2_sc := Nat.add_pos_left (Nat.mul_pos ((hDp_nat_pos hp)) h2bp) _
        exact div_pos (by exact_mod_cast hp) (mul_pos hDp hDx)
      have hpa_le_pb_sc : pa_sc ≤ pb_sc := by
        have : (pa_n : ℝ) ≤ pb_n := by
          have h1 := le_trans hpa_le (le_trans (le_of_lt h12) hpb_ge)
          rw [div_le_div_iff_of_pos_right hDp] at h1; exact h1
        exact Nat.mul_le_mul_right D_x (by exact_mod_cast this)
      have hdx2_ge : ∀ x3 ∈ Icc m1 m2, φ2 - (y 0 + y 1 + y 2) - x3 ≤ (denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x) := by
        intro x3 hx3
        have heq : (denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x) = (n2b : ℝ) / D_x + (pb - pa) := by
          dsimp only [denom_x2_sc]; rw [Nat.cast_add, Nat.cast_sub hpa_le_pb_sc]
          dsimp only [pa, pb, pa_sc, pb_sc]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        rw [heq]; rw [hm1_eq] at hx3; linarith [hx3.1, hy2.2]
      have hdx3_ge : ∀ x3 ∈ Icc m1 m2, x3 ≤ (denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x) := by
        intro x3 hx3
        have h1 : x3 ≤ C_R := le_trans hx3.2 (hm2_eq ▸ by linarith)
        have h2 : x3 ≤ pb - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) :=
          le_trans hx3.2 (hm2_eq ▸ by linarith [hy0.1, hy1.1, hy2.1])
        dsimp only [denom_x3_sc]
        by_cases hmn : C_sc ≤ pb_sc - s_min_n
        · rw [min_eq_left hmn]
          have : (C_sc : ℝ) / ((D_p : ℝ) * D_x) = C_R := by rw [(C_sc_cast hp)]; dsimp only [Params4DT.C_R]; field_simp [ne_of_gt hDp]
          rw [this]; exact h1
        · rw [min_eq_right (le_of_not_ge hmn)]
          have hle_s : s_min_n ≤ pb_sc := by push Not at hnotz; omega
          have : ((pb_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) =
              pb - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) := by
            rw [Nat.cast_sub hle_s]; dsimp only [pb_sc, s_min_n, pb]; push_cast
            field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          rw [this]; exact h2
      have hc2 : ContinuousOn (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc m1 m2) :=
        continuousOn_const.div (by fun_prop) (fun x3 hx3 => by
          have : 0 < x3 := lt_of_lt_of_le (lt_of_lt_of_le hBpos hBm1) hx3.1
          have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by rw [hm2_eq] at hx3; linarith [hx3.2]
          positivity)
      have hmono := intervalIntegral.integral_mono_on hm12 (intervalIntegrable_const : IntervalIntegrable (fun _ => 1 / (((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))) volume m1 m2) (hc2.intervalIntegrable_of_Icc hm12)
        (fun x3 hx3 => by
          have hx3p : 0 < x3 := lt_of_lt_of_le (lt_of_lt_of_le hBpos hBm1) hx3.1
          have hremp : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by rw [hm2_eq] at hx3; linarith [hx3.2]
          exact div_le_div₀ (by norm_num) (le_refl 1) (mul_pos hx3p hremp)
            (mul_le_mul (hdx3_ge x3 hx3) (hdx2_ge x3 hx3) (le_of_lt hremp) (le_of_lt hdx3_pos)))
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono
      rw [le_div_iff₀ h12pos]
      have hmul := mul_le_mul_of_nonneg_left hmono (show (0 : ℝ) ≤ 1 / (y 0 * y 1 * y 2) by positivity)
      refine le_trans ?_ hmul
      dsimp only [gain_c]
      have h012_le : y 0 * y 1 * y 2 ≤ ((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) := by
        have h01 := mul_le_mul hy0.2 hy1.2 (le_of_lt hy1p) (by positivity)
        exact mul_le_mul h01 hy2.2 (le_of_lt hy2p) (by positivity)
      have hden_le : y 0 * y 1 * y 2 * (((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x))) ≤
          ((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) * ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)) := by
        have := mul_le_mul_of_nonneg_right h012_le (mul_nonneg (le_of_lt hdx3_pos) (le_of_lt hdx2_pos))
        linarith
      have hdiv := div_le_div₀ (by norm_num) (le_refl 1) (mul_pos (mul_pos (mul_pos hy0p hy1p) hy2p) (mul_pos hdx3_pos hdx2_pos)) hden_le
      have hstep := mul_le_mul_of_nonneg_right hdiv (le_of_lt h12pos)
      refine le_trans hstep (le_of_eq ?_)
      field_simp [ne_of_gt hy0p, ne_of_gt hy1p, ne_of_gt hy2p, ne_of_gt hdx3_pos, ne_of_gt hdx2_pos]; try ring
    dsimp only [gain_fn, mmGainFn]
    by_cases hcond : s_max_n + C_sc ≤ pb_sc ∨ pa_sc ≤ s_min_n + B_sc
    · rw [if_pos hcond]; exact hnonneg_rhs
    · rw [if_neg hcond]
      cases knd with
      | box =>
        change Pslab_in.indicator (fun _ => gain_c) y ≤ _
        by_cases hyP : y ∈ Pslab_in
        · rw [Set.indicator_of_mem hyP]; exact hcore (le_of_lt hyP.1) hyP.2 hcond
        · rw [Set.indicator_of_notMem hyP]; exact hnonneg_rhs
      | tri01 | tri12 | simp =>
        split_ifs with hin
        · exact hcore
            (by
              have h' : (pb_sc : ℝ) ≤ ((s_min_n + C_sc : ℕ) : ℝ) := by exact_mod_cast hin.1
              dsimp only [pb_sc, s_min_n] at h'; push_cast [(C_sc_cast hp)] at h'
              have hmul : (pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
                  (pb_n : ℝ) * D_x - ((D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a) + (D_p : ℝ) * C_n) := by
                have hgen : ∀ (P a b c d Dp Dx : ℝ), Dp ≠ 0 → Dx ≠ 0 →
                    (P / Dp - d / Dx - (a / Dx + b / Dx + 2 * (c / Dx))) * (Dp * Dx) = P * Dx - (Dp * (a + b + 2 * c) + Dp * d) := by
                  intro P a b c d Dp Dx h1 h2; field_simp [h1, h2]; try ring
                exact hgen pb_n n0a n1a n2a C_n D_p D_x (ne_of_gt hDp) (ne_of_gt hDx)
              have hle0 : pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) ≤ 0 :=
                nonpos_of_mul_nonpos_left (by rw [hmul]; linarith only [h']) (mul_pos hDp hDx)
              linarith only [hle0, hy0.1, hy1.1, hy2.1])
            (by
              have h' : ((s_max_n + B_sc : ℕ) : ℝ) ≤ (pa_sc : ℝ) := by exact_mod_cast hin.2
              dsimp only [pa_sc, s_max_n] at h'; push_cast [(B_sc_cast hp)] at h'
              have hmul : (pa - B_R - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
                  (pa_n : ℝ) * D_x - ((D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * B_n) := by
                have hgen : ∀ (P a b c d Dp Dx : ℝ), Dp ≠ 0 → Dx ≠ 0 →
                    (P / Dp - d / Dx - (a / Dx + b / Dx + 2 * (c / Dx))) * (Dp * Dx) = P * Dx - (Dp * (a + b + 2 * c) + Dp * d) := by
                  intro P a b c d Dp Dx h1 h2; field_simp [h1, h2]; try ring
                exact hgen pa_n n0b n1b n2b B_n D_p D_x (ne_of_gt hDp) (ne_of_gt hDx)
              have hge0 : 0 ≤ pa - B_R - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x)) :=
                nonneg_of_mul_nonneg_left (by rw [hmul]; linarith only [h']) (mul_pos hDp hDx)
              linarith only [hge0, hy0.2, hy1.2, hy2.2])
            hcond
        · exact hnonneg_rhs
  exact hgain_lb

private lemma cell3_Mm_pt {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ∀ y ∈ cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1) ≤
        mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b y - mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y := by
  intro y hy
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  have hy2p : 0 < y 2 := by
    rcases hv with ⟨_, _, _, _, _, _, hA2, _, _, ht01, ht12, hts⟩
    have hmem2 : (n2a : ℝ) / D_x ≤ y 2 := by
      cases knd with
      | box => exact hy.2.2.1
      | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact hy.2.2.1.1
      | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact hy.2.2.1.1
      | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact hy.2.2.1.1
    exact lt_of_lt_of_le (hA_pos hp) (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt (hDx_pos hp))) hmem2)
  have hsub := G_fn_sub_eq hp h12 hy2p
  dsimp only at hsub
  have hsub' : G_fn φ1 y - G_fn φ2 y =
      (φ2 - φ1) * (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) -
      (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) := by linarith only [hsub]
  rw [hsub']
  have hsplit : ((1 / (y 0 * y 1 * y 2)) *
      ((φ2 - φ1) * (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) -
       (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))))) / (φ2 - φ1) =
      (1 / (y 0 * y 1 * y 2)) * (∫ x3 in B_R..(max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) -
      ((1 / (y 0 * y 1 * y 2)) * (∫ x3 in (max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2)))..(max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))),
        1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3)))) / (φ2 - φ1) := by
    field_simp [ne_of_gt h12pos]
  rw [hsplit]
  have hd := cell3_Mm_pt_drop hp hpa_le h12 hpb_ge hv hy
  have hg := cell3_Mm_pt_gain hp hpa_le h12 hpb_ge hv hy
  linarith only [hd, hg]

private lemma cell3_Mm_pos_interior {pa_n pb_n : ℕ}
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    (h1 : ¬ pb_n * D_x ≤ D_p * (n0a + n1a + 2 * n2a) + B_sc)
    (h2 : D_p * (n0b + n1b + 2 * n2b) + C_sc ≤ pa_n * D_x) :
    let pa : ℝ := (pa_n : ℝ) / D_p
    let pa_sc := pa_n * D_x
    let f3 (a0 a1 a2 : Nat) : Nat :=
      let rb := pa_sc - D_p * (a0 + a1 + a2 + B_n)
      let rc := pa_sc - D_p * (a0 + a1 + a2 + C_n)
      ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * B_n * rb * rb) +
      ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * C_n * rc * rc)
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      ((C_R - B_R) / 2) *
        (1 / (y 0 * y 1 * y 2 * B_R * (pa - (y 0 + y 1 + y 2) - B_R) ^ 2) +
         1 / (y 0 * y 1 * y 2 * C_R * (pa - (y 0 + y 1 + y 2) - C_R) ^ 2)) ≤
      (ceilDiv (S_3 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (C_n - B_n) * sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b)
        (2 * facDen knd * nVerts3 knd * D_x4 * S_v) : ℝ) / S_3 := by
  dsimp only
  have hdrop_cont : ContinuousOn (mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :=
    mmDropFn_continuousOn hp hv
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab_in : Set (Fin 3 → ℝ) := {y | pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R}
  set denom_x3_sc := min C_sc (pb_sc - s_min_n)
  set denom_x2_sc := D_p * n2b + (pb_sc - pa_sc)
  let drop_fn : (Fin 3 → ℝ) → ℝ := mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b
  let gain_c : ℝ := 1 / (((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) *
    ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
  have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
  have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
  have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
  have hpa_ge : (n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R ≤ pa := by
    have h' : ((s_max_n + C_sc : ℕ) : ℝ) ≤ (pa_sc : ℝ) := by exact_mod_cast h2
    dsimp only [s_max_n, pa_sc] at h'; push_cast [(C_sc_cast hp)] at h'
    have : (pa - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + C_R)) * ((D_p : ℝ) * D_x) =
        (pa_n : ℝ) * D_x - ((D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b) + (D_p : ℝ) * C_n) := by
      dsimp only [pa, Params4DT.C_R]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    nlinarith [mul_pos hDp hDx]
  let fB : (Fin 3 → ℝ) → ℝ := fun y => 1 / (y 0 * y 1 * y 2 * B_R * (pa - (y 0 + y 1 + y 2) - B_R) ^ 2)
  let fC : (Fin 3 → ℝ) → ℝ := fun y => 1 / (y 0 * y 1 * y 2 * C_R * (pa - (y 0 + y 1 + y 2) - C_R) ^ 2)
  have hconv_one : ∀ M : ℝ, 0 < M → M ≤ C_R → ConvexOn ℝ C (fun y => 1 / (y 0 * y 1 * y 2 * M * (pa - (y 0 + y 1 + y 2) - M) ^ 2)) := by
    intro M hMp hMC
    let L : Fin 5 → (Fin 3 → ℝ) → ℝ :=
      ![fun y => y 0, fun y => y 1, fun y => y 2, fun y => pa - (y 0 + y 1 + y 2) - M, fun y => pa - (y 0 + y 1 + y 2) - M]
    have hfeq : (fun y : Fin 3 → ℝ => 1 / (y 0 * y 1 * y 2 * M * (pa - (y 0 + y 1 + y 2) - M) ^ 2)) =
        fun y => (1 / M) • (∏ i : Fin 5, L i y)⁻¹ := by
      ext y; dsimp only [L]; rw [Fin.prod_univ_five, smul_eq_mul, sq]; simp; ring
    rw [hfeq]
    exact (convexOn_inv_prod (cell3Set_convex knd _ _ _ _ _ _) L
      (fun i _ _ _ _ a b _ _ hab => by have ha1 : a = 1 - b := (by linarith only [hab]); fin_cases i <;> simp [L, smul_eq_mul] <;> (rw [ha1]; ring))
      (fun i y hy => by
        rcases hmem y hy with ⟨hy0, hy1, hy2⟩; rcases hmem_simp y hy with ⟨h0, h1', h2'⟩
        fin_cases i <;> dsimp only [L]
        · exact lt_of_lt_of_le (hA_pos hp) h0.1
        · exact lt_of_lt_of_le (hA_pos hp) h1'.1
        · exact lt_of_lt_of_le (hA_pos hp) h2'.1
        · change 0 < pa - (y 0 + y 1 + y 2) - M; linarith only [hy0.2, hy1.2, hy2.2, h2'.1, (hA_pos hp), hpa_ge, hMC]
        · change 0 < pa - (y 0 + y 1 + y 2) - M; linarith only [hy0.2, hy1.2, hy2.2, h2'.1, (hA_pos hp), hpa_ge, hMC])).smul (by positivity)
  have hconv_tot : ConvexOn ℝ C (fun y => ((C_R - B_R) / 2) * (fB y + fC y)) :=
    ((hconv_one B_R hBpos (le_of_lt (hBC_lt hp))).add (hconv_one C_R hCpos (le_refl _))).smul (by linarith [(hBC_lt hp)])
  have hcont_tot : ContinuousOn (fun y => ((C_R - B_R) / 2) * (fB y + fC y)) C := by
    dsimp only [drop_fn, mmDropFn] at hdrop_cont; rw [if_neg h1, if_pos h2] at hdrop_cont; exact hdrop_cont
  have hhh := hh_cell3 knd hok hconv_tot hcont_tot
  have hv_le : ∀ a0 a1 a2 : ℕ, 0 < a0 → 0 < a1 → 0 < a2 → a0 ≤ n0b → a1 ≤ n1b → a2 ≤ n2b →
      fB ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x] + fC ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x] ≤
        ((ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * B_n * (pa_sc - D_p * (a0 + a1 + a2 + B_n)) * (pa_sc - D_p * (a0 + a1 + a2 + B_n))) +
          ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * C_n * (pa_sc - D_p * (a0 + a1 + a2 + C_n)) * (pa_sc - D_p * (a0 + a1 + a2 + C_n))) : ℕ) : ℝ) / S_v := by
    intro a0 a1 a2 ha0 ha1 ha2 hle0 hle1 hle2
    have hterm : ∀ M_n : ℕ, 0 < M_n → M_n ≤ C_n →
        1 / (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((M_n : ℝ) / D_x) *
          (pa - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x) - (M_n : ℝ) / D_x) ^ 2) ≤
        (ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * M_n * (pa_sc - D_p * (a0 + a1 + a2 + M_n)) * (pa_sc - D_p * (a0 + a1 + a2 + M_n))) : ℝ) / S_v := by
      intro M_n hMp hMC
      have hsub_lt : D_p * (a0 + a1 + a2 + M_n) < pa_sc := by
        have h1' : a0 + a1 + a2 + M_n < n0b + n1b + 2 * n2b + C_n := by omega
        have h2' : D_p * (a0 + a1 + a2 + M_n) < s_max_n + C_sc := by
          dsimp only [s_max_n]; rw [hCsc_eq hp, ← Nat.mul_add]; exact Nat.mul_lt_mul_of_pos_left h1' ((hDp_nat_pos hp))
        omega
      set rM := pa_sc - D_p * (a0 + a1 + a2 + M_n)
      have hrM_pos : 0 < rM := Nat.sub_pos_of_lt hsub_lt
      have hden_pos : 0 < a0 * a1 * a2 * M_n * rM * rM := by positivity
      have hcd : ((S_v * D_x6 * D_p2 : ℕ) : ℝ) ≤ ((a0 * a1 * a2 * M_n * rM * rM : ℕ) : ℝ) *
          (ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * M_n * rM * rM) : ℝ) := by exact_mod_cast le_mul_ceilDiv hden_pos
      have hrM_r : pa - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x) - (M_n : ℝ) / D_x = (rM : ℝ) / ((D_p : ℝ) * D_x) := by
        dsimp only [rM]; rw [Nat.cast_sub (le_of_lt hsub_lt)]; dsimp only [pa, pa_sc]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      rw [hrM_r, div_le_div_iff₀ (by positivity) (hSv_pos hp)]
      have : (1 : ℝ) * S_v * ((D_x : ℝ) ^ 6 * (D_p : ℝ) ^ 2) = ((S_v * D_x6 * D_p2 : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, (D_x6_cast hp), (D_p2_cast hp)]; ring
      have : (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((M_n : ℝ) / D_x) * ((rM : ℝ) / ((D_p : ℝ) * D_x)) ^ 2) *
          ((D_x : ℝ) ^ 6 * (D_p : ℝ) ^ 2) = ((a0 * a1 * a2 * M_n * rM * rM : ℕ) : ℝ) := by
        push_cast; field_simp [ne_of_gt hDx, ne_of_gt hDp]; try ring
      nlinarith [show (0 : ℝ) < (D_x : ℝ) ^ 6 * (D_p : ℝ) ^ 2 by positivity]
    push_cast; simp only [add_div]
    have t1 := hterm B_n (B_n_pos hp) (by exact le_of_lt (hBC_nat hp))
    have t2 := hterm C_n (by exact (C_n_pos hp)) (le_refl _)
    dsimp only [fB, fC, Params4DT.B_R, Params4DT.C_R]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linarith
  set f3 := fun (a0 a1 a2 : ℕ) =>
    ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * B_n * (pa_sc - D_p * (a0 + a1 + a2 + B_n)) * (pa_sc - D_p * (a0 + a1 + a2 + B_n))) +
    ceilDiv (S_v * D_x6 * D_p2) (a0 * a1 * a2 * C_n * (pa_sc - D_p * (a0 + a1 + a2 + C_n)) * (pa_sc - D_p * (a0 + a1 + a2 + C_n)))
  have hsum_le :
      sumVerts3R (fun y => ((C_R - B_R) / 2) * (fB y + fC y)) knd
        ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ≤
      ((C_R - B_R) / 2) * ((sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b : ℝ) / S_v) := by
    have hCB_nn : 0 ≤ (C_R - B_R) / 2 := by linarith [(hBC_lt hp)]
    have hpull : sumVerts3R (fun y => ((C_R - B_R) / 2) * (fB y + fC y)) knd
        ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) =
        ((C_R - B_R) / 2) * sumVerts3R (fun y => fB y + fC y) knd
        ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
      cases knd <;> simp [sumVerts3R] <;> ring
    rw [hpull]
    refine mul_le_mul_of_nonneg_left ?_ hCB_nn
    refine sumVerts3R_le knd ht01 ht12 hts (fun a0 a1 a2 ha0 ha1 ha2 => ?_)
    exact hv_le a0 a1 a2 (by rcases ha0 with rfl | rfl <;> assumption) (by rcases ha1 with rfl | rfl <;> assumption)
      (by rcases ha2 with rfl | rfl <;> assumption) (by rcases ha0 with rfl | rfl <;> omega)
      (by rcases ha1 with rfl | rfl <;> omega) (by rcases ha2 with rfl | rfl <;> omega)
  have hvol_nn : 0 ≤ ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
      ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ)) := by
    have : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
    have : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
    have : (0 : ℝ) ≤ (n0b : ℝ) / D_x - (n0a : ℝ) / D_x := sub_nonneg.mpr h0le_r
    have : (0 : ℝ) ≤ (n1b : ℝ) / D_x - (n1a : ℝ) / D_x := sub_nonneg.mpr h1le_r
    have : (0 : ℝ) ≤ (n2b : ℝ) / D_x - (n2a : ℝ) / D_x := sub_nonneg.mpr h2le_r
    positivity
  refine le_trans (le_trans hhh (mul_le_mul_of_nonneg_left hsum_le hvol_nn)) ?_
  set sv := sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b
  have hden_nat : 0 < 2 * facDen knd * nVerts3 knd * D_x4 * S_v :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by cases knd <;> simp [facDen])) (by cases knd <;> simp [nVerts3])) (hDx4_nat_pos hp)) (hSv_nat_pos hp)
  have hcd : ((S_3 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (C_n - B_n) * sv : ℕ) : ℝ) ≤
      ((2 * facDen knd * nVerts3 knd * D_x4 * S_v : ℕ) : ℝ) *
      (ceilDiv (S_3 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (C_n - B_n) * sv)
        (2 * facDen knd * nVerts3 knd * D_x4 * S_v) : ℝ) := by exact_mod_cast le_mul_ceilDiv hden_nat
  have hfd_pos : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
  have hnv_pos : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
  rw [le_div_iff₀ (hS3_pos hp)]
  have hLHS : ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
      ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ)) *
      (((C_R - B_R) / 2) * ((sv : ℝ) / S_v)) * S_3 =
      ((S_3 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (C_n - B_n) * sv : ℕ) : ℝ) /
      ((2 * facDen knd * nVerts3 knd * D_x4 * S_v : ℕ) : ℝ) := by
    dsimp only [Params4DT.C_R, Params4DT.B_R]; simp only [Nat.cast_mul, (D_x4_cast hp)]
    rw [Nat.cast_sub h0le, Nat.cast_sub h1le, Nat.cast_sub h2le, Nat.cast_sub (show B_n ≤ C_n by exact le_of_lt (hBC_nat hp))]
    exact mm_pos_int_alg n0a n0b n1a n1b n2a n2b B_n C_n sv D_x (facDen knd) (nVerts3 knd) S_v S_3 (ne_of_gt hDx) (ne_of_gt hfd_pos) (ne_of_gt hnv_pos) (ne_of_gt (hSv_pos hp))
  rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith

private lemma cell3_Mm_pos_slab {pa_n pb_n : ℕ}
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b)
    (h1 : ¬ pb_n * D_x ≤ D_p * (n0a + n1a + 2 * n2a) + B_sc) :
    let pb : ℝ := (pb_n : ℝ) / D_p
    let s_min_n := D_p * (n0a + n1a + 2 * n2a)
    let pb_sc := pb_n * D_x
    let rn := ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - B_sc - s_min_n) -
              ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n)
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      (max 0 (pb - B_R - (y 0 + y 1 + 2 * y 2)) - max 0 (pb - C_R - (y 0 + y 1 + 2 * y 2))) /
        (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R) ≤
      (ceilDiv (S_3 * D_x2 * rn) (48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n2a * B_n) : ℝ) / S_3 := by
  dsimp only
  have hdrop_cont : ContinuousOn (mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) :=
    mmDropFn_continuousOn hp hv
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab_in : Set (Fin 3 → ℝ) := {y | pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R}
  set denom_x3_sc := min C_sc (pb_sc - s_min_n)
  set denom_x2_sc := D_p * n2b + (pb_sc - pa_sc)
  let drop_fn : (Fin 3 → ℝ) → ℝ := mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b
  let gain_c : ℝ := 1 / (((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) *
    ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
  have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
  have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
  have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
  let g : ℝ → ℝ := fun s => max 0 (pb - B_R - s) - max 0 (pb - C_R - s)
  have hgnn : ∀ s, 0 ≤ g s := fun s => by
    dsimp only [g]; linarith [max_le_max_left 0 (show pb - C_R - s ≤ pb - B_R - s by linarith [(hBC_lt hp)])]
  have hganti : Antitone g := fun s1 s2 hs => by
    dsimp only [g]
    by_cases hc1 : 0 ≤ pb - C_R - s2
    · rw [max_eq_right hc1,
          max_eq_right (show (0 : ℝ) ≤ pb - B_R - s2 by linarith only [hc1, (hBC_lt hp)]),
          max_eq_right (show (0 : ℝ) ≤ pb - C_R - s1 by linarith only [hc1, hs]),
          max_eq_right (show (0 : ℝ) ≤ pb - B_R - s1 by linarith only [hc1, hs, (hBC_lt hp)])]; linarith
    · push Not at hc1; rw [max_eq_left (le_of_lt hc1)]
      by_cases hc2 : pb - C_R - s1 ≤ 0
      · rw [max_eq_left hc2]; linarith [max_le_max_left 0 (show pb - B_R - s2 ≤ pb - B_R - s1 by linarith only [hs])]
      · push Not at hc2
        rw [max_eq_right (le_of_lt hc2),
            max_eq_right (show (0 : ℝ) ≤ pb - B_R - s1 by linarith only [hc2, (hBC_lt hp)])]
        have hle : max 0 (pb - B_R - s2) ≤ C_R - B_R :=
          max_le (by linarith only [(hBC_lt hp)]) (by linarith only [hc1])
        linarith only [hle]
  have hs3 := s3_antitone_le knd hok hgnn hganti
    ((Continuous.continuousOn (by dsimp only [g]; fun_prop)).integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _))
  rw [integral_div]
  have hden_pos : 0 < ((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R := by positivity
  have hle1 : (∫ y in C, g (y 0 + y 1 + 2 * y 2)) / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R) ≤
      ((1 / (facDen knd : ℝ)) * ∫ y in cell3Set .box ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x), g (y 0 + y 1 + 2 * y 2)) /
        (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R) :=
    div_le_div_of_nonneg_right hs3 (le_of_lt hden_pos)
  have hbox_eq : ∫ y in cell3Set .box ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x), g (y 0 + y 1 + 2 * y 2) =
      ((ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - B_sc - s_min_n) : ℝ) -
       (ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n) : ℝ)) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
    dsimp only [g]
    rw [integral_sub
      ((Continuous.continuousOn (by fun_prop)).integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _))
      ((Continuous.continuousOn (by fun_prop)).integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)),
      int_ramp_box3_eq h0le_r h1le_r h2le_r, int_ramp_box3_eq h0le_r h1le_r h2le_r,
      hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le]
    push Not at h1
    have hR1 : pb - B_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
        ((pb_sc - B_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      dsimp only [pb, Params4DT.B_R, pb_sc, s_min_n]; push_cast [(B_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have hR2_eq : ramp3SumR (((n0b - n0a : ℕ) : ℝ) / D_x) (((n1b - n1a : ℕ) : ℝ) / D_x) (2 * (((n2b - n2a : ℕ) : ℝ) / D_x))
        (pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) / 48 =
        (ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n) : ℝ) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
      by_cases hge2 : C_sc + s_min_n ≤ pb_sc
      · have hR2 : pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
            ((pb_sc - C_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          dsimp only [pb, Params4DT.C_R, pb_sc, s_min_n]; push_cast [(C_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        rw [hR2, ← ramp3Num_eq hp]
      · push Not at hge2
        have hz : pb_sc - C_sc - s_min_n = 0 := by omega
        rw [hz]; simp only [Buchstab4DT.ramp3Num, beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div]
        have hneg : pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) ≤ 0 := by
          have hlt : (pb_sc : ℝ) < ((C_sc + s_min_n : ℕ) : ℝ) := by exact_mod_cast hge2
          dsimp only [pb_sc, s_min_n] at hlt; push_cast [(C_sc_cast hp)] at hlt
          have : (pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
              (pb_n : ℝ) * D_x - ((D_p : ℝ) * C_n + (D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a)) := by
            dsimp only [pb, Params4DT.C_R]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          nlinarith [mul_pos hDp hDx]
        dsimp only [ramp3SumR]
        have : (0 : ℝ) ≤ ((n0b - n0a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
        have : (0 : ℝ) ≤ ((n1b - n1a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
        have : (0 : ℝ) ≤ 2 * (((n2b - n2a : ℕ) : ℝ) / D_x) := mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))
        rw [max_eq_left hneg, max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
            max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [hR1, ← ramp3Num_eq hp, hR2_eq]; ring
  rw [hbox_eq] at hle1
  set r1 := ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - B_sc - s_min_n)
  set r2 := ramp3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n)
  have hr2_le_r1 : r2 ≤ r1 := by
    have hnn : 0 ≤ ((r1 : ℝ) - r2) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
      rw [← hbox_eq]
      exact setIntegral_nonneg (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet (fun y _ => hgnn _)
    have : (0 : ℝ) ≤ (r1 : ℝ) - r2 := by
      have := mul_nonneg hnn (show (0 : ℝ) ≤ 48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4 by positivity)
      have hring : ((r1 : ℝ) - r2) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) * (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) = (r1 : ℝ) - r2 := by
        field_simp [ne_of_gt hDp, ne_of_gt hDx]
      linarith
    exact_mod_cast (sub_nonneg.mp this)
  refine le_trans hle1 ?_
  have hden_nat : 0 < 48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n2a * B_n :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by cases knd <;> simp [facDen])) (hDp4_nat_pos hp)) h0p) h1p) h2p) h2p) h2p) (B_n_pos hp)
  have hcd : ((S_3 * D_x2 * (r1 - r2) : ℕ) : ℝ) ≤
      ((48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n2a * B_n : ℕ) : ℝ) *
      (ceilDiv (S_3 * D_x2 * (r1 - r2)) (48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n2a * B_n) : ℝ) := by
    exact_mod_cast le_mul_ceilDiv hden_nat
  have hfd_p : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
  rw [le_div_iff₀ (hS3_pos hp)]
  have hLHS : ((1 / (facDen knd : ℝ)) * (((r1 : ℝ) - r2) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4))) /
      (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 3 * B_R) * S_3 =
      ((S_3 * D_x2 * (r1 - r2) : ℕ) : ℝ) /
      ((48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n2a * B_n : ℕ) : ℝ) := by
    dsimp only [Params4DT.B_R]; simp only [Nat.cast_mul, (D_x2_cast hp), (D_p4_cast hp)]; rw [Nat.cast_sub hr2_le_r1]
    have h0r : (0 : ℝ) < n0a := Nat.cast_pos.mpr h0p
    have h1r : (0 : ℝ) < n1a := Nat.cast_pos.mpr h1p
    have h2r : (0 : ℝ) < n2a := Nat.cast_pos.mpr h2p
    have hBr : (0 : ℝ) < B_n := Nat.cast_pos.mpr (B_n_pos hp)
    have hgen : ∀ (x0 x1 x2 Bn Dx Dp fd v1 v2 S3 : ℝ), Dx ≠ 0 → Dp ≠ 0 → fd ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → Bn ≠ 0 →
        1 / fd * ((v1 - v2) / (48 * Dp ^ 4 * Dx ^ 4)) / (x0 / Dx * (x1 / Dx) * (x2 / Dx) ^ 3 * (Bn / Dx)) * S3 =
        (S3 * Dx ^ 2 * (v1 - v2)) / (48 * fd * Dp ^ 4 * x0 * x1 * x2 * x2 * x2 * Bn) := by
      intro x0 x1 x2 Bn Dx Dp fd v1 v2 S3 h1 h2 h3 h4 h5 h6 h7; field_simp [h1, h2, h3, h4, h5, h6, h7]; try ring
    exact hgen n0a n1a n2a B_n D_x D_p (facDen knd) r1 r2 S_3 (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt hfd_p) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt hBr)
  rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith

private lemma cell3_Mm_pos_bound {pa_n pb_n : ℕ}
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b y ≤
      ((evalMmLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b).1 : ℝ) / S_3 := by
  dsimp only [mmDropFn, Buchstab4DT.evalMmLeaf]
  by_cases h1 : pb_n * D_x ≤ D_p * (n0a + n1a + 2 * n2a) + B_sc
  · rw [if_pos h1, if_pos h1]; simp
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : D_p * (n0b + n1b + 2 * n2b) + C_sc ≤ pa_n * D_x
    · rw [if_pos h2, if_pos h2]; exact cell3_Mm_pos_interior hp hv h1 h2
    · rw [if_neg h2, if_neg h2]; exact cell3_Mm_pos_slab hp (pa_n := pa_n) hv h1

private lemma cell3_Mm_neg_bound {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    ((evalMmLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b).2 : ℝ) / S_3 ≤
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  have hok := cell3Valid_ok hp hv
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hCpos : 0 < C_R := lt_trans hBpos (hBC_lt hp)
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hmem : ∀ y ∈ C,
      y 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      y 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      y 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) := by
    intro y hy; cases knd with
    | box => exact hy
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hy.1, hy.2.1, hy.2.2.1⟩
  have hmem_simp : ∀ y ∈ C, y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    intro y hy; rcases hmem y hy with ⟨h0, h1, h2⟩
    exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) h0.1,
            le_trans h0.2 (div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) h1.1,
            le_trans h1.2 (div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx))⟩,
           ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) h2.1,
            le_trans h2.2 (div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx))⟩⟩
  set pa : ℝ := (pa_n : ℝ) / D_p
  set pb : ℝ := (pb_n : ℝ) / D_p
  set s_min_n := D_p * (n0a + n1a + 2 * n2a)
  set s_max_n := D_p * (n0b + n1b + 2 * n2b)
  set pa_sc := pa_n * D_x
  set pb_sc := pb_n * D_x
  set Pslab_in : Set (Fin 3 → ℝ) := {y | pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R}
  set denom_x3_sc := min C_sc (pb_sc - s_min_n)
  set denom_x2_sc := D_p * n2b + (pb_sc - pa_sc)
  let drop_fn : (Fin 3 → ℝ) → ℝ := mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b
  let gain_c : ℝ := 1 / (((n0b : ℝ) / D_x) * ((n1b : ℝ) / D_x) * ((n2b : ℝ) / D_x) *
    ((denom_x3_sc : ℝ) / ((D_p : ℝ) * D_x)) * ((denom_x2_sc : ℝ) / ((D_p : ℝ) * D_x)))
  let gain_fn : (Fin 3 → ℝ) → ℝ := mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b
  have h0le_r : (n0a : ℝ) / D_x ≤ (n0b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx)
  have h1le_r : (n1a : ℝ) / D_x ≤ (n1b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx)
  have h2le_r : (n2a : ℝ) / D_x ≤ (n2b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx)
  have hdx : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := fun a b hab => by rw [Nat.cast_sub hab]; ring
  dsimp only [Buchstab4DT.evalMmLeaf, mmGainFn]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hcond : s_max_n + C_sc ≤ pb_sc ∨ pa_sc ≤ s_min_n + B_sc
  · rw [if_pos hcond, if_pos hcond]; simp
  · rw [if_neg hcond, if_neg hcond]
    push Not at hcond
    have hpa_le_pb_sc : pa_sc ≤ pb_sc := by
      have h1 : (pa_n : ℝ) ≤ pb_n := by
        have := le_trans hpa_le (le_trans (le_of_lt h12) hpb_ge)
        rwa [div_le_div_iff_of_pos_right hDp] at this
      exact Nat.mul_le_mul_right D_x (by exact_mod_cast h1)
    have hdx3_p : 0 < denom_x3_sc := by
      dsimp only [denom_x3_sc]; exact lt_min ((hCsc_nat_pos hp)) (by omega)
    have hdx2_p : 0 < denom_x2_sc := Nat.add_pos_left (Nat.mul_pos ((hDp_nat_pos hp)) h2bp) _
    by_cases hk : knd = .box
    · subst hk
      change _ ≤ ∫ y in C, Pslab_in.indicator (fun _ => gain_c) y
      -- Exact cut3 difference on box!
      have hR1 : pa - B_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
          ((pa_sc - B_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        dsimp only [pa, Params4DT.B_R, pa_sc, s_min_n]; push_cast [(B_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      have hR2_eq : cut3SumR (((n0b - n0a : ℕ) : ℝ) / D_x) (((n1b - n1a : ℕ) : ℝ) / D_x) (2 * (((n2b - n2a : ℕ) : ℝ) / D_x))
          (pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) / 12 =
          (cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n) : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) := by
        by_cases hge2 : C_sc + s_min_n ≤ pb_sc
        · have hR2 : pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) =
              ((pb_sc - C_sc - s_min_n : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            dsimp only [pb, Params4DT.C_R, pb_sc, s_min_n]; push_cast [(C_sc_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          rw [hR2, ← cut3Num_eq hp]
        · push Not at hge2
          have hz : pb_sc - C_sc - s_min_n = 0 := by omega
          rw [hz]; simp only [Buchstab4DT.cut3Num, beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div]
          have hneg : pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x)) ≤ 0 := by
            have hlt : (pb_sc : ℝ) < ((C_sc + s_min_n : ℕ) : ℝ) := by exact_mod_cast hge2
            dsimp only [pb_sc, s_min_n] at hlt; push_cast [(C_sc_cast hp)] at hlt
            have : (pb - C_R - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x))) * ((D_p : ℝ) * D_x) =
                (pb_n : ℝ) * D_x - ((D_p : ℝ) * C_n + (D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a)) := by
              dsimp only [pb, Params4DT.C_R]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
            nlinarith [mul_pos hDp hDx]
          dsimp only [cut3SumR]
          have : (0 : ℝ) ≤ ((n0b - n0a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
          have : (0 : ℝ) ≤ ((n1b - n1a : ℕ) : ℝ) / D_x := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)
          have : (0 : ℝ) ≤ 2 * (((n2b - n2a : ℕ) : ℝ) / D_x) := mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))
          rw [max_eq_left hneg, max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
              max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
      set c1 := cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pa_sc - B_sc - s_min_n)
      set c2 := cut3Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (pb_sc - C_sc - s_min_n)
      by_cases hle_c : c1 ≤ c2
      · have : c1 - c2 = 0 := Nat.sub_eq_zero_of_le hle_c
        rw [this]; simp only [mul_zero, Nat.zero_div, Nat.cast_zero, zero_div]
        exact setIntegral_nonneg hCmeas (fun y _ => Set.indicator_nonneg (fun _ _ => by
          dsimp only [gain_c]
          exact div_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx))
            (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)))
            (div_nonneg (Nat.cast_nonneg _) (le_of_lt hDx)))
            (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hDp) (le_of_lt hDx))))
            (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hDp) (le_of_lt hDx))))) y)
      · push Not at hle_c
        -- Notice: Pslab_in = {y | pb - C_R < y0+y1+2*y2 ∧ y0+y1+2*y2 ≤ pa - B_R}!
        -- If pa - B_R < pb - C_R then Pslab_in is empty, AND c1 ≤ c2 (contradicting hle_c)!
        -- Wait: prove pb - C_R ≤ pa - B_R directly from c2 < c1!
        have hpbC_le_paB : pb - C_R ≤ pa - B_R := by
          by_contra hgt; push Not at hgt
          have hi_a : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - B_R}).indicator (fun _ => (1 : ℝ))) C volume :=
            (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator (isClosed_le (by fun_prop) continuous_const).measurableSet
          have hi_b : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - C_R}).indicator (fun _ => (1 : ℝ))) C volume :=
            (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator (isClosed_le (by fun_prop) continuous_const).measurableSet
          have hle_i : ∫ y in C, ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - B_R}).indicator (fun _ => (1 : ℝ)) y ≤
              ∫ y in C, ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - C_R}).indicator (fun _ => (1 : ℝ)) y := by
            refine setIntegral_mono_on hi_a hi_b hCmeas (fun y _ => ?_)
            simp only [Set.indicator, mem_ofPred_eq]; split_ifs with h' h'' <;> try norm_num
            exfalso; exact h'' (le_trans h' (le_of_lt hgt))
          rw [vol_cut_box3_eq h0le_r h1le_r h2le_r, vol_cut_box3_eq h0le_r h1le_r h2le_r,
              hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le, hR1, ← cut3Num_eq hp, hR2_eq] at hle_i
          have : (c1 : ℝ) ≤ c2 := by
            have hpos : (0 : ℝ) < 12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3 := by positivity
            have := mul_le_mul_of_nonneg_right hle_i (le_of_lt hpos)
            rwa [div_mul_cancel₀ _ (ne_of_gt hpos), div_mul_cancel₀ _ (ne_of_gt hpos)] at this
          have : c1 ≤ c2 := by exact_mod_cast this
          omega
        have hind_eq : ∀ y : Fin 3 → ℝ, Pslab_in.indicator (fun _ => gain_c) y =
            gain_c * (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - B_R}).indicator (fun _ => (1 : ℝ)) y -
                      ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - C_R}).indicator (fun _ => (1 : ℝ)) y) := by
          intro y; simp only [Pslab_in, Set.indicator, mem_ofPred_eq]
          by_cases h1 : y 0 + y 1 + 2 * y 2 ≤ pa - B_R
          · by_cases h2 : y 0 + y 1 + 2 * y 2 ≤ pb - C_R
            · have hn : ¬ (pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R) := fun h => not_lt_of_ge h2 h.1
              simp [h1, h2, hn]
            · have hy' : pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R := ⟨lt_of_not_ge h2, h1⟩
              simp [h1, h2, hy']
          · have h2 : ¬ (y 0 + y 1 + 2 * y 2 ≤ pb - C_R) := fun h => h1 (le_trans h hpbC_le_paB)
            have hn : ¬ (pb - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ pa - B_R) := fun h => h1 h.2
            simp [h1, h2, hn]
        simp_rw [hind_eq]
        have hi_hi : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pa - B_R}).indicator (fun _ => (1 : ℝ))) C volume :=
          (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator (isClosed_le (by fun_prop) continuous_const).measurableSet
        have hi_lo : IntegrableOn (({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ pb - C_R}).indicator (fun _ => (1 : ℝ))) C volume :=
          (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator (isClosed_le (by fun_prop) continuous_const).measurableSet
        rw [integral_const_mul, integral_sub hi_hi hi_lo,
            vol_cut_box3_eq h0le_r h1le_r h2le_r, vol_cut_box3_eq h0le_r h1le_r h2le_r,
            hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le, hR1, ← cut3Num_eq hp, hR2_eq]
        have hden_nat : 0 < 12 * D_p * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc :=
          Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (hDp_nat_pos hp)) h0bp) h1bp) h2bp) hdx3_p) hdx2_p
        have hfl : ((S_3 * D_x2 * (c1 - c2) / (12 * D_p * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc) : ℕ) : ℝ) *
            ((12 * D_p * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc : ℕ) : ℝ) ≤ ((S_3 * D_x2 * (c1 - c2) : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self _ _
        have hRHS_eq : gain_c * ((c1 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) - (c2 : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3)) =
            ((S_3 * D_x2 * (c1 - c2) : ℕ) : ℝ) / (((12 * D_p * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc : ℕ) : ℝ) * S_3) := by
          dsimp only [gain_c]; simp only [Nat.cast_mul, (D_x2_cast hp)]; rw [Nat.cast_sub (le_of_lt hle_c)]
          have h0r : (0 : ℝ) < n0b := Nat.cast_pos.mpr h0bp
          have h1r : (0 : ℝ) < n1b := Nat.cast_pos.mpr h1bp
          have h2r : (0 : ℝ) < n2b := Nat.cast_pos.mpr h2bp
          have hd3 : (0 : ℝ) < denom_x3_sc := Nat.cast_pos.mpr hdx3_p
          have hd2 : (0 : ℝ) < denom_x2_sc := Nat.cast_pos.mpr hdx2_p
          have hgen : ∀ (x0 x1 x2 d3 d2 Dx Dp v1 v2 S3 : ℝ), Dx ≠ 0 → Dp ≠ 0 → S3 ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → d3 ≠ 0 → d2 ≠ 0 →
              1 / (x0 / Dx * (x1 / Dx) * (x2 / Dx) * (d3 / (Dp * Dx)) * (d2 / (Dp * Dx))) *
                (v1 / (12 * Dp ^ 3 * Dx ^ 3) - v2 / (12 * Dp ^ 3 * Dx ^ 3)) =
              (S3 * Dx ^ 2 * (v1 - v2)) / (12 * Dp * x0 * x1 * x2 * d3 * d2 * S3) := by
            intro x0 x1 x2 d3 d2 Dx Dp v1 v2 S3 h1 h2 h3 h4 h5 h6 h7 h8; field_simp [h1, h2, h3, h4, h5, h6, h7, h8]; try ring
          exact hgen n0b n1b n2b denom_x3_sc denom_x2_sc D_x D_p c1 c2 S_3 (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt (hS3_pos hp)) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt hd3) (ne_of_gt hd2)
        rw [hRHS_eq, div_le_div_iff₀ (hS3_pos hp) (mul_pos (by exact_mod_cast hden_nat) (hS3_pos hp)), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hfl (le_of_lt (hS3_pos hp))
    · suffices hgoal :
          ((if pb_sc ≤ s_min_n + C_sc ∧ s_max_n + B_sc ≤ pa_sc then
              (S_3 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a)) /
                (facDen knd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc)
            else 0 : ℕ) : ℝ) / S_3 ≤
          ∫ y in C, (if pb_sc ≤ s_min_n + C_sc ∧ s_max_n + B_sc ≤ pa_sc then fun _ => gain_c else fun _ => 0) y by
        cases knd with
        | box => exact absurd rfl hk
        | tri01 => simpa only [Bool.and_eq_true, decide_eq_true_eq] using hgoal
        | tri12 => simpa only [Bool.and_eq_true, decide_eq_true_eq] using hgoal
        | simp => simpa only [Bool.and_eq_true, decide_eq_true_eq] using hgoal
      by_cases hin : pb_sc ≤ s_min_n + C_sc ∧ s_max_n + B_sc ≤ pa_sc
      · simp only [Bool.and_eq_true, decide_eq_true_eq, hin, ↓reduceIte, and_self]
        have hvol_eq : ∫ _ in C, gain_c =
            (((n0b - n0a : ℕ) : ℝ) / D_x) * (((n1b - n1a : ℕ) : ℝ) / D_x) * (((n2b - n2a : ℕ) : ℝ) / D_x) / (facDen knd : ℝ) * gain_c := by
          have h1 := hh_cell3 knd hok (convexOn_const gain_c (cell3Set_convex knd _ _ _ _ _ _)) continuousOn_const
          have h2 := jensen_cell3 knd hok (convexOn_const gain_c (cell3Set_convex knd _ _ _ _ _ _)) continuousOn_const
          have hsum_c : sumVerts3R (fun _ => gain_c) knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) =
              (nVerts3 knd : ℝ) * gain_c := by cases knd <;> simp [sumVerts3R, nVerts3] <;> ring
          rw [hsum_c] at h1
          rw [hdx n0a n0b h0le, hdx n1a n1b h1le, hdx n2a n2b h2le] at h1 h2
          have hnv_ne : (nVerts3 knd : ℝ) ≠ 0 := by cases knd <;> simp [nVerts3]
          exact le_antisymm (le_trans h1 (le_of_eq (by field_simp [hnv_ne]))) h2
        rw [hvol_eq]
        have hden_nat : 0 < facDen knd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc :=
          Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by cases knd <;> simp [facDen]) h0bp) h1bp) h2bp) hdx3_p) hdx2_p
        have hfl : ((S_3 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) /
            (facDen knd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc) : ℕ) : ℝ) *
            ((facDen knd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc : ℕ) : ℝ) ≤
            ((S_3 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self _ _
        have hRHS_eq : (((n0b - n0a : ℕ) : ℝ) / D_x) * (((n1b - n1a : ℕ) : ℝ) / D_x) * (((n2b - n2a : ℕ) : ℝ) / D_x) / (facDen knd : ℝ) * gain_c =
            ((S_3 * D_x2 * D_p2 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) : ℕ) : ℝ) /
            (((facDen knd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc : ℕ) : ℝ) * S_3) := by
          dsimp only [gain_c]; simp only [Nat.cast_mul, (D_x2_cast hp), (D_p2_cast hp)]
          have hfd_p : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
          have h0r : (0 : ℝ) < n0b := Nat.cast_pos.mpr h0bp
          have h1r : (0 : ℝ) < n1b := Nat.cast_pos.mpr h1bp
          have h2r : (0 : ℝ) < n2b := Nat.cast_pos.mpr h2bp
          have hd3 : (0 : ℝ) < denom_x3_sc := Nat.cast_pos.mpr hdx3_p
          have hd2 : (0 : ℝ) < denom_x2_sc := Nat.cast_pos.mpr hdx2_p
          have hgen : ∀ (dx0 dx1 dx2 x0 x1 x2 d3 d2 Dx Dp fd S3 : ℝ),
              Dx ≠ 0 → Dp ≠ 0 → S3 ≠ 0 → fd ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → d3 ≠ 0 → d2 ≠ 0 →
              dx0 / Dx * (dx1 / Dx) * (dx2 / Dx) / fd *
                (1 / (x0 / Dx * (x1 / Dx) * (x2 / Dx) * (d3 / (Dp * Dx)) * (d2 / (Dp * Dx)))) =
              (S3 * Dx ^ 2 * Dp ^ 2 * dx0 * dx1 * dx2) / (fd * x0 * x1 * x2 * d3 * d2 * S3) := by
            intro dx0 dx1 dx2 x0 x1 x2 d3 d2 Dx Dp fd S3 h1 h2 h3 h4 h5 h6 h7 h8 h9
            field_simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]; try ring
          exact hgen (n0b - n0a : ℕ) (n1b - n1a : ℕ) (n2b - n2a : ℕ) n0b n1b n2b denom_x3_sc denom_x2_sc D_x D_p (facDen knd) S_3
            (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt (hS3_pos hp)) (ne_of_gt hfd_p) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt hd3) (ne_of_gt hd2)
        rw [hRHS_eq, div_le_div_iff₀ (hS3_pos hp) (mul_pos (by exact_mod_cast hden_nat) (hS3_pos hp)), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hfl (le_of_lt (hS3_pos hp))
      · simp only [Bool.and_eq_true, decide_eq_true_eq, hin, ↓reduceIte]; simp


private lemma cell3_Mm_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {φ1 φ2 : ℝ}
    (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p)
    (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    let r := evalMmLeaf pa_n pb_n knd n0a n0b n1a n1b n2a n2b
    ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x),
      ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1) ≤
      ((r.1 : ℝ) - (r.2 : ℝ)) / S_3 := by
  set C := cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  have hdrop_int : IntegrableOn (mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b) C volume :=
    (mmDropFn_continuousOn hp hv).integrableOn_compact (cell3Set_isCompact knd _ _ _ _ _ _)
  have hgain_int : IntegrableOn (mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b) C volume := by
    unfold mmGainFn; dsimp only
    by_cases hcond : D_p * (n0b + n1b + 2 * n2b) + C_sc ≤ pb_n * D_x ∨ pa_n * D_x ≤ D_p * (n0a + n1a + 2 * n2a) + B_sc
    · rw [if_pos hcond]; exact continuousOn_const.integrableOn_compact (cell3Set_isCompact knd _ _ _ _ _ _)
    · rw [if_neg hcond]
      cases knd with
      | box =>
        have hPslab_m : MeasurableSet {y : Fin 3 → ℝ | (pb_n : ℝ) / D_p - C_R < y 0 + y 1 + 2 * y 2 ∧ y 0 + y 1 + 2 * y 2 ≤ (pa_n : ℝ) / D_p - B_R} :=
          show MeasurableSet ({y : Fin 3 → ℝ | (pb_n : ℝ) / D_p - C_R < y 0 + y 1 + 2 * y 2} ∩ {y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ (pa_n : ℝ) / D_p - B_R}) from
            (isOpen_lt continuous_const (by fun_prop : Continuous fun y : Fin 3 → ℝ => y 0 + y 1 + 2 * y 2)).measurableSet.inter
              (isClosed_le (by fun_prop : Continuous fun y : Fin 3 → ℝ => y 0 + y 1 + 2 * y 2) continuous_const).measurableSet
        exact (continuousOn_const.integrableOn_compact (cell3Set_isCompact .box _ _ _ _ _ _)).indicator hPslab_m
      | _ => split_ifs <;> exact continuousOn_const.integrableOn_compact (cell3Set_isCompact _ _ _ _ _ _ _)
  have hG_int : IntegrableOn (fun y => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1)) C volume := by
    have h1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) hv
    have h2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) hv
    have heq : (fun y : Fin 3 → ℝ => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1)) =
        fun y => ((1 / (y 0 * y 1 * y 2)) * G_fn φ1 y - (1 / (y 0 * y 1 * y 2)) * G_fn φ2 y) / (φ2 - φ1) := by ext y; ring
    rw [heq]; exact (h1.sub h2).div_const _
  have hint_le : ∫ y in C, ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1) ≤
      (∫ y in C, mmDropFn p pa_n pb_n n0a n0b n1a n1b n2a n2b y) - (∫ y in C, mmGainFn p pa_n pb_n knd n0a n0b n1a n1b n2a n2b y) := by
    rw [← integral_sub hdrop_int hgain_int]
    exact setIntegral_mono_on hG_int (hdrop_int.sub hgain_int) hCmeas (cell3_Mm_pt hp hpa_le h12 hpb_ge hv)
  have hpos := cell3_Mm_pos_bound hp (pa_n := pa_n) (pb_n := pb_n) hv
  have hneg := cell3_Mm_neg_bound hp hpa_le h12 hpb_ge hv
  dsimp only; rw [sub_div]; linarith only [hint_le, hpos, hneg]

/-! ### Part 7: Interval Chaining Lemmas & Main `solution` Theorem -/

private lemma root3Valid : cell3Valid .simp A_n B_n A_n B_n A_n B_n :=
  ⟨le_refl _, by exact le_of_lt (hAB_nat hp), le_refl _, le_refl _, by exact le_of_lt (hAB_nat hp), le_refl _,
   le_refl _, by exact le_of_lt (hAB_nat hp), le_refl _, by simp, by simp, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

private lemma root4Valid : cell4Valid .simp A_n B_n A_n B_n A_n B_n B_n C_n :=
  ⟨(root3Valid hp), le_refl _, by exact le_of_lt (hBC_nat hp), le_refl _⟩

private lemma diff_le_Mp {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {t : BoxTree3}
    (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv : tree3Valid .simp t = true)
    {φ1 φ2 : ℝ} (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p) :
    let r := evalTree3 (evalMpLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n
    I_fn ω φ2 - I_fn ω φ1 ≤ (φ2 - φ1) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) := by
  intro r
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  rw [I_fn_eq_G hp hω (le_trans hpb_ge hpb_top), I_fn_eq_G hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top))]
  have h1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) (root3Valid hp)
  have h2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) (root3Valid hp)
  dsimp only [Params4DT.A_R, Params4DT.B_R] at *
  have hsub : (∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), (1 / (y 0 * y 1 * y 2)) * G_fn φ2 y) -
      (∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), (1 / (y 0 * y 1 * y 2)) * G_fn φ1 y) =
      (φ2 - φ1) * ∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1) := by
    rw [← integral_sub h2 h1, integral_div, mul_div_cancel₀ _ (ne_of_gt h12pos)]
    apply setIntegral_congr_fun (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet
    intro y _; ring
  rw [hsub]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h12pos)
  exact evalTree3_sound hp
    (fun knd a0 b0 a1 b1 a2 b2 hv => by
      have hi1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) hv
      have hi2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) hv
      have heq : (fun y : Fin 3 → ℝ => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ2 y - G_fn φ1 y)) / (φ2 - φ1)) =
          fun y => ((1 / (y 0 * y 1 * y 2)) * G_fn φ2 y - (1 / (y 0 * y 1 * y 2)) * G_fn φ1 y) / (φ2 - φ1) := by ext y; ring
      rw [heq]; exact (hi2.sub hi1).div_const _)
    (evalMpLeaf pa_n pb_n)
    (fun knd a0 b0 a1 b1 a2 b2 hv => cell3_Mp_leaf_sound hp hω hpa_le h12 hpb_ge hpb_top hv)
    t .simp A_n B_n A_n B_n A_n B_n htv (root3Valid hp)

private lemma diff_le_Mm {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {t : BoxTree3}
    (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv : tree3Valid .simp t = true)
    {φ1 φ2 : ℝ} (hpa_le : (pa_n : ℝ) / D_p ≤ φ1) (h12 : φ1 < φ2) (hpb_ge : φ2 ≤ (pb_n : ℝ) / D_p) :
    let r := evalTree3 (evalMmLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n
    I_fn ω φ1 - I_fn ω φ2 ≤ (φ2 - φ1) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) := by
  intro r
  have h12pos : 0 < φ2 - φ1 := sub_pos.mpr h12
  rw [I_fn_eq_G hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)), I_fn_eq_G hp hω (le_trans hpb_ge hpb_top)]
  have h1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) (root3Valid hp)
  have h2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) (root3Valid hp)
  dsimp only [Params4DT.A_R, Params4DT.B_R] at *
  have hsub : (∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), (1 / (y 0 * y 1 * y 2)) * G_fn φ1 y) -
      (∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), (1 / (y 0 * y 1 * y 2)) * G_fn φ2 y) =
      (φ2 - φ1) * ∫ y in cell3Set .simp ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x) ((A_n : ℝ) / D_x) ((B_n : ℝ) / D_x), ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1) := by
    rw [← integral_sub h1 h2, integral_div, mul_div_cancel₀ _ (ne_of_gt h12pos)]
    apply setIntegral_congr_fun (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet
    intro y _; ring
  rw [hsub]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h12pos)
  exact evalTree3_sound hp
    (fun knd a0 b0 a1 b1 a2 b2 hv => by
      have hi1 := G_fn_integrableOn hp hω (le_trans (le_of_lt h12) (le_trans hpb_ge hpb_top)) hv
      have hi2 := G_fn_integrableOn hp hω (le_trans hpb_ge hpb_top) hv
      have heq : (fun y : Fin 3 → ℝ => ((1 / (y 0 * y 1 * y 2)) * (G_fn φ1 y - G_fn φ2 y)) / (φ2 - φ1)) =
          fun y => ((1 / (y 0 * y 1 * y 2)) * G_fn φ1 y - (1 / (y 0 * y 1 * y 2)) * G_fn φ2 y) / (φ2 - φ1) := by ext y; ring
      rw [heq]; exact (hi1.sub hi2).div_const _)
    (evalMmLeaf pa_n pb_n)
    (fun knd a0 b0 a1 b1 a2 b2 hv => cell3_Mm_leaf_sound hp hω hpa_le h12 hpb_ge hpb_top hv)
    t .simp A_n B_n A_n B_n A_n B_n htv (root3Valid hp)

lemma monotone_interval {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {t : BoxTree3}
    (_hpa_le_pb : pa_n ≤ pb_n) (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv : tree3Valid .simp t = true)
    (hok : let r := evalTree3 (evalMmLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n; r.1 ≤ r.2)
    {φ : ℝ} (hlo : (pa_n : ℝ) / D_p ≤ φ) (hhi : φ ≤ (pb_n : ℝ) / D_p) :
    I_fn ω φ ≤ I_fn ω ((pb_n : ℝ) / D_p) := by
  by_cases heq : φ = (pb_n : ℝ) / D_p
  · rw [heq]
  · have hlt : φ < (pb_n : ℝ) / D_p := lt_of_le_of_ne hhi heq
    have hd := diff_le_Mm hp hω hpb_top htv hlo hlt (le_refl _)
    set r := evalTree3 (evalMmLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n
    have hr_le : (r.1 : ℝ) - (r.2 : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hok)
    have hmul : ((pb_n : ℝ) / D_p - φ) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hhi) (div_nonpos_of_nonpos_of_nonneg hr_le (le_of_lt (hS3_pos hp)))
    linarith

lemma antitone_interval {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n pb_n : ℕ} {t : BoxTree3}
    (_hpa_le_pb : pa_n ≤ pb_n) (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv : tree3Valid .simp t = true)
    (hok : let r := evalTree3 (evalMpLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n; r.1 ≤ r.2)
    {φ : ℝ} (hlo : (pa_n : ℝ) / D_p ≤ φ) (hhi : φ ≤ (pb_n : ℝ) / D_p) :
    I_fn ω φ ≤ I_fn ω ((pa_n : ℝ) / D_p) := by
  by_cases heq : φ = (pa_n : ℝ) / D_p
  · rw [heq]
  · have hlt : (pa_n : ℝ) / D_p < φ := lt_of_le_of_ne hlo (Ne.symm heq)
    have hd := diff_le_Mp hp hω hpb_top htv (le_refl _) hlt hhi
    set r := evalTree3 (evalMpLeaf pa_n pb_n) .simp t A_n B_n A_n B_n A_n B_n
    have hr_le : (r.1 : ℝ) - (r.2 : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hok)
    have hmul : (φ - (pa_n : ℝ) / D_p) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) (div_nonpos_of_nonpos_of_nonneg hr_le (le_of_lt (hS3_pos hp)))
    linarith

lemma peak_left_bound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {bnd_n pa_n ps_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4}
    (hpa_le_ps : pa_n ≤ ps_n) (hps_top : (ps_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv3 : tree3Valid .simp t3 = true) (htv4 : tree4Valid .simp t4 = true)
    (hok : let r := evalTree3 (evalMmLeaf pa_n ps_n) .simp t3 A_n B_n A_n B_n A_n B_n
           let v := evalTree4 (eval4Leaf ps_n) .simp t4 A_n B_n A_n B_n A_n B_n B_n C_n
           v * D_p + (r.1 - r.2) * (ps_n - pa_n) * 100 ≤ bnd_n * D_p)
    {φ : ℝ} (hlo : (pa_n : ℝ) / D_p ≤ φ) (hhi : φ ≤ (ps_n : ℝ) / D_p) :
    I_fn ω φ ≤ (bnd_n : ℝ) / S_4 := by
  set r := evalTree3 (evalMmLeaf pa_n ps_n) .simp t3 A_n B_n A_n B_n A_n B_n
  set v := evalTree4 (eval4Leaf ps_n) .simp t4 A_n B_n A_n B_n A_n B_n B_n C_n
  have h4 : I_fn ω ((ps_n : ℝ) / D_p) ≤ (v : ℝ) / S_4 :=
    evalTree4_sound hp hω (eval4Leaf ps_n) ((ps_n : ℝ) / D_p)
      (fun knd a0 b0 a1 b1 a2 b2 a3 b3 hv => cell4_leaf_sound hp hω hps_top hv)
      t4 .simp A_n B_n A_n B_n A_n B_n B_n C_n htv4 (root4Valid hp)
  have hdiff : I_fn ω φ - I_fn ω ((ps_n : ℝ) / D_p) ≤
      (((ps_n - pa_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) := by
    by_cases heq : φ = (ps_n : ℝ) / D_p
    · rw [heq, sub_self]; positivity
    · have hd := diff_le_Mm hp hω hps_top htv3 hlo (lt_of_le_of_ne hhi heq) (le_refl _)
      have hr_le : (r.1 : ℝ) - (r.2 : ℝ) ≤ ((r.1 - r.2 : ℕ) : ℝ) := by
        by_cases h12 : r.2 ≤ r.1
        · rw [Nat.cast_sub h12]
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h12), Nat.cast_zero]
          have : (r.1 : ℝ) ≤ r.2 := by exact_mod_cast le_of_not_ge h12
          linarith
      have hlen_le : (ps_n : ℝ) / D_p - φ ≤ ((ps_n - pa_n : ℕ) : ℝ) / D_p := by
        rw [Nat.cast_sub hpa_le_ps, sub_div]; linarith
      have h1 : ((ps_n : ℝ) / D_p - φ) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) ≤
          ((ps_n : ℝ) / D_p - φ) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr_le (le_of_lt (hS3_pos hp))) (sub_nonneg.mpr hhi)
      have h2 : ((ps_n : ℝ) / D_p - φ) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) ≤
          (((ps_n - pa_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) :=
        mul_le_mul_of_nonneg_right hlen_le (by positivity)
      linarith
  have hok_r : ((v * D_p + (r.1 - r.2) * (ps_n - pa_n) * 100 : ℕ) : ℝ) ≤ ((bnd_n * D_p : ℕ) : ℝ) := by
    exact_mod_cast hok
  push_cast at hok_r
  have hS_ratio : (S_4 : ℝ) = (S_3 : ℝ) * 100 := by rw [hS4_eq hp]; push_cast; ring
  have hsum_le : (v : ℝ) / S_4 + (((ps_n - pa_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) ≤ (bnd_n : ℝ) / S_4 := by
    have hpos : (0 : ℝ) < (S_4 : ℝ) * D_p := mul_pos (hS4_pos hp) (hDp_pos hp)
    rw [← mul_le_mul_iff_right₀ hpos]
    have hl : (S_4 : ℝ) * D_p * ((v : ℝ) / S_4 + (((ps_n - pa_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3)) =
        (v : ℝ) * D_p + ((r.1 - r.2 : ℕ) : ℝ) * ((ps_n - pa_n : ℕ) : ℝ) * 100 := by
      rw [hS_ratio]; field_simp [ne_of_gt (hS3_pos hp), ne_of_gt (hDp_pos hp)]; try ring
    have hr : (S_4 : ℝ) * D_p * ((bnd_n : ℝ) / S_4) = (bnd_n : ℝ) * D_p := by
      field_simp [ne_of_gt (hS4_pos hp)]
    rw [hl, hr]; linarith
  linarith

lemma peak_right_bound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {bnd_n ps_n pb_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4}
    (hps_le_pb : ps_n ≤ pb_n) (hpb_top : (pb_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    (htv3 : tree3Valid .simp t3 = true) (htv4 : tree4Valid .simp t4 = true)
    (hok : let r := evalTree3 (evalMpLeaf ps_n pb_n) .simp t3 A_n B_n A_n B_n A_n B_n
           let v := evalTree4 (eval4Leaf ps_n) .simp t4 A_n B_n A_n B_n A_n B_n B_n C_n
           v * D_p + (r.1 - r.2) * (pb_n - ps_n) * 100 ≤ bnd_n * D_p)
    {φ : ℝ} (hlo : (ps_n : ℝ) / D_p ≤ φ) (hhi : φ ≤ (pb_n : ℝ) / D_p) :
    I_fn ω φ ≤ (bnd_n : ℝ) / S_4 := by
  set r := evalTree3 (evalMpLeaf ps_n pb_n) .simp t3 A_n B_n A_n B_n A_n B_n
  set v := evalTree4 (eval4Leaf ps_n) .simp t4 A_n B_n A_n B_n A_n B_n B_n C_n
  have hps_top : (ps_n : ℝ) / D_p ≤ 5 * A_R + B_R :=
    le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hps_le_pb) (le_of_lt (hDp_pos hp))) hpb_top
  have h4 : I_fn ω ((ps_n : ℝ) / D_p) ≤ (v : ℝ) / S_4 :=
    evalTree4_sound hp hω (eval4Leaf ps_n) ((ps_n : ℝ) / D_p)
      (fun knd a0 b0 a1 b1 a2 b2 a3 b3 hv => cell4_leaf_sound hp hω hps_top hv)
      t4 .simp A_n B_n A_n B_n A_n B_n B_n C_n htv4 (root4Valid hp)
  have hdiff : I_fn ω φ - I_fn ω ((ps_n : ℝ) / D_p) ≤
      (((pb_n - ps_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) := by
    by_cases heq : φ = (ps_n : ℝ) / D_p
    · rw [heq, sub_self]; positivity
    · have hd := diff_le_Mp hp hω hpb_top htv3 (le_refl _) (lt_of_le_of_ne hlo (Ne.symm heq)) hhi
      have hr_le : (r.1 : ℝ) - (r.2 : ℝ) ≤ ((r.1 - r.2 : ℕ) : ℝ) := by
        by_cases h12 : r.2 ≤ r.1
        · rw [Nat.cast_sub h12]
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h12), Nat.cast_zero]
          have : (r.1 : ℝ) ≤ r.2 := by exact_mod_cast le_of_not_ge h12
          linarith
      have hlen_le : φ - (ps_n : ℝ) / D_p ≤ ((pb_n - ps_n : ℕ) : ℝ) / D_p := by
        rw [Nat.cast_sub hps_le_pb, sub_div]; linarith
      have h1 : (φ - (ps_n : ℝ) / D_p) * (((r.1 : ℝ) - (r.2 : ℝ)) / S_3) ≤
          (φ - (ps_n : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr_le (le_of_lt (hS3_pos hp))) (sub_nonneg.mpr hlo)
      have h2 : (φ - (ps_n : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) ≤
          (((pb_n - ps_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) :=
        mul_le_mul_of_nonneg_right hlen_le (by positivity)
      linarith
  have hok_r : ((v * D_p + (r.1 - r.2) * (pb_n - ps_n) * 100 : ℕ) : ℝ) ≤ ((bnd_n * D_p : ℕ) : ℝ) := by
    exact_mod_cast hok
  push_cast at hok_r
  have hS_ratio : (S_4 : ℝ) = (S_3 : ℝ) * 100 := by rw [hS4_eq hp]; push_cast; ring
  have hsum_le : (v : ℝ) / S_4 + (((pb_n - ps_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3) ≤ (bnd_n : ℝ) / S_4 := by
    have hpos : (0 : ℝ) < (S_4 : ℝ) * D_p := mul_pos (hS4_pos hp) (hDp_pos hp)
    rw [← mul_le_mul_iff_right₀ hpos]
    have hl : (S_4 : ℝ) * D_p * ((v : ℝ) / S_4 + (((pb_n - ps_n : ℕ) : ℝ) / D_p) * (((r.1 - r.2 : ℕ) : ℝ) / S_3)) =
        (v : ℝ) * D_p + ((r.1 - r.2 : ℕ) : ℝ) * ((pb_n - ps_n : ℕ) : ℝ) * 100 := by
      rw [hS_ratio]; field_simp [ne_of_gt (hS3_pos hp), ne_of_gt (hDp_pos hp)]; try ring
    have hr : (S_4 : ℝ) * D_p * ((bnd_n : ℝ) / S_4) = (bnd_n : ℝ) * D_p := by
      field_simp [ne_of_gt (hS4_pos hp)]
    rw [hl, hr]; linarith
  linarith

lemma trans_bound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {bnd_n pa_n : ℕ} {t4 : BoxTree4}
    (hpa_ge : D_p * (4 * B_n + C_n) ≤ pa_n * D_x)
    (htv4 : tree4Valid .simp t4 = true)
    (hok : evalTree4 (eval4TransLeaf pa_n) .simp t4 A_n B_n A_n B_n A_n B_n B_n C_n ≤ bnd_n)
    {φ : ℝ} (hlo : (pa_n : ℝ) / D_p ≤ φ) :
    I_fn ω φ ≤ (bnd_n : ℝ) / S_4 := by
  have h4 := evalTree4_sound hp hω (eval4TransLeaf pa_n) φ
    (fun knd a0 b0 a1 b1 a2 b2 a3 b3 hv => cell4_trans_leaf_sound hp hω hlo hpa_ge hv)
    t4 .simp A_n B_n A_n B_n A_n B_n B_n C_n htv4 (root4Valid hp)
  refine le_trans h4 ?_
  exact div_le_div_of_nonneg_right (by exact_mod_cast hok) (le_of_lt (hS4_pos hp))


end

end Sol_Buchstab4DT_Chaining

theorem solution :
∀ (p : Params4DT), p.Valid → ∀ {ω : ℝ → ℝ}, IsBuchstabCore ω →
  (∀ {pa_n pb_n : ℕ} {t : BoxTree3},
    pa_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t = true →
    (let r := evalTree3 (evalMmLeaf p pa_n pb_n) .simp t p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n; r.1 ≤ r.2) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ I_fn p ω ((pb_n : ℝ) / p.D_p)) ∧
  (∀ {pa_n pb_n : ℕ} {t : BoxTree3},
    pa_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t = true →
    (let r := evalTree3 (evalMpLeaf p pa_n pb_n) .simp t p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n; r.1 ≤ r.2) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ I_fn p ω ((pa_n : ℝ) / p.D_p)) ∧
  (∀ {bnd_n pa_n ps_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4},
    pa_n ≤ ps_n → (ps_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t3 = true → tree4Valid .simp t4 = true →
    (let r := evalTree3 (evalMmLeaf p pa_n ps_n) .simp t3 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n
     let v := evalTree4 (eval4Leaf p ps_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n
     v * p.D_p + (r.1 - r.2) * (ps_n - pa_n) * 100 ≤ bnd_n * p.D_p) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (ps_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) ∧
  (∀ {bnd_n ps_n pb_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4},
    ps_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t3 = true → tree4Valid .simp t4 = true →
    (let r := evalTree3 (evalMpLeaf p ps_n pb_n) .simp t3 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n
     let v := evalTree4 (eval4Leaf p ps_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n
     v * p.D_p + (r.1 - r.2) * (pb_n - ps_n) * 100 ≤ bnd_n * p.D_p) →
    ∀ {φ : ℝ}, (ps_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) ∧
  (∀ {bnd_n pa_n : ℕ} {t4 : BoxTree4},
    p.D_p * (4 * p.B_n + p.C_n) ≤ pa_n * p.D_x →
    tree4Valid .simp t4 = true →
    evalTree4 (eval4TransLeaf p pa_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n ≤ bnd_n →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) := fun p hp {_} hω =>
  ⟨@Sol_Buchstab4DT_Chaining.monotone_interval p hp _ hω,
   @Sol_Buchstab4DT_Chaining.antitone_interval p hp _ hω,
   @Sol_Buchstab4DT_Chaining.peak_left_bound p hp _ hω,
   @Sol_Buchstab4DT_Chaining.peak_right_bound p hp _ hω,
   @Sol_Buchstab4DT_Chaining.trans_bound p hp _ hω⟩
