-- Prove2me | solution 1 for buchstab4dt_sound4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:36:54.022196+00:00
-- url     : https://prove2.me/submissions/41636be3-75cd-4930-af5c-b88b0508d044

import Mathlib
import Definitions.Def_Buchstab4DT_Core
import Theorems.Thm_buchstab4dt_geom

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

namespace Sol_Buchstab4DT_Sound4

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

private lemma setIntegral_union_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : Set α} {f : α → ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnnB : ∀ x ∈ B, 0 ≤ f x) (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) :
    ∫ x in A ∪ B, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) := by
  rw [← union_diff_self, setIntegral_union disjoint_sdiff_self_right (hB.diff hA) hintA (hintB.mono_set diff_subset)]
  have hle : ∫ x in B \ A, f x ∂μ ≤ ∫ x in B, f x ∂μ :=
    setIntegral_mono_set hintB (ae_restrict_of_forall_mem hB hnnB) (Filter.Eventually.of_forall diff_subset)
  linarith

private lemma setIntegral_le_sum2_4 {A B D : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hD : D ⊆ A ∪ B) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnnA : ∀ x ∈ A, 0 ≤ f x) (hnnB : ∀ x ∈ B, 0 ≤ f x)
    (hintA : IntegrableOn f A volume) (hintB : IntegrableOn f B volume) :
    ∫ x in D, f x ≤ (∫ x in A, f x) + (∫ x in B, f x) := by
  have hun_nn : ∀ x ∈ A ∪ B, 0 ≤ f x := by rintro x (hx | hx); exact hnnA x hx; exact hnnB x hx
  have h1 : ∫ x in D, f x ≤ ∫ x in A ∪ B, f x :=
    setIntegral_mono_set (hintA.union hintB)
      (ae_restrict_of_forall_mem (hA.union hB) hun_nn) (Filter.Eventually.of_forall hD)
  exact le_trans h1 (setIntegral_union_le_of_nonneg hA hB hnnB hintA hintB)


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

/-! ### Part 5: Nat-to-Real Bridge for `cut3Num`, `ramp3Num`, `cut4Num`, and Leaf Bounds -/

lemma cut3Num_eq {dx0 dx1 dx2 r : ℕ} :
    ((cut3Num dx0 dx1 dx2 r : ℝ) / (12 * (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3)) =
      cut3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 12 := by
  have hDp : (0 : ℝ) < D_p := (hDp_pos hp)
  have hDx : (0 : ℝ) < D_x := (hDx_pos hp)
  have hsc : ∀ h : ℕ, ((r - h : ℕ) : ℝ) / ((D_p : ℝ) * D_x) = max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x)) := by
    intro h
    by_cases hle : h ≤ r
    · rw [Nat.cast_sub hle, max_eq_right (sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)))]
      ring
    · push Not at hle
      rw [Nat.sub_eq_zero_of_le (le_of_lt hle), Nat.cast_zero, zero_div,
          max_eq_left (sub_nonpos.mpr (div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt hle) (by positivity)))]
  have hsum_eq : cut3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) =
      ((cut3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
       (cut3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ)) / ((D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) := by
    have hsp : ∀ h : ℕ, (max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x))) ^ 3 =
        (subPow3 r h : ℝ) / ((D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) := by
      intro h; rw [← hsc h]; unfold subPow3; push_cast; ring
    dsimp only [cut3SumR, cut3Pos, cut3Neg]
    have e0 : (r : ℝ) / ((D_p : ℝ) * D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by simp
    have e1 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e2 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e3 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e4 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e5 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e6 : (r : ℝ) / ((D_p : ℝ) * D_x) - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e7 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    rw [e7, e1, e2, e3, e4, e5, e6, hsp, hsp, hsp, hsp, hsp, hsp, hsp, e0, hsp]
    push_cast; ring
  have hvol_nn : 0 ≤ cut3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 12 := by
    have hv := vol_cut_box3_eq (a0 := 0) (b0 := (dx0 : ℝ) / D_x) (a1 := 0) (b1 := (dx1 : ℝ) / D_x)
      (a2 := 0) (b2 := (dx2 : ℝ) / D_x) (L := (r : ℝ) / ((D_p : ℝ) * D_x)) (by positivity) (by positivity) (by positivity)
    simp only [sub_zero, zero_add, mul_zero] at hv
    rw [← hv]
    exact setIntegral_nonneg (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet (fun x _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  have hge_nat : cut3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r ≤ cut3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r := by
    have hdiff_nn : (0 : ℝ) ≤ (cut3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
        (cut3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) := by
      rw [hsum_eq] at hvol_nn
      have hden : (0 : ℝ) < (D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3 * 12 := by positivity
      have := mul_nonneg hvol_nn (le_of_lt hden)
      have hring : ((cut3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
          (cut3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ)) / ((D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3) / 12 *
          ((D_p : ℝ) ^ 3 * (D_x : ℝ) ^ 3 * 12) =
          (cut3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
          (cut3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) := by field_simp [ne_of_gt hDp, ne_of_gt hDx]
      linarith
    exact_mod_cast (sub_nonneg.mp hdiff_nn)
  unfold Buchstab4DT.cut3Num
  by_cases hr0 : r = 0
  · subst hr0; simp only [beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div] at hsum_eq ⊢
    rw [hsum_eq]; unfold cut3Pos cut3Neg subPow3; simp
  · simp only [beq_iff_eq, hr0, ↓reduceIte]
    split_ifs with hfull
    · have hv := vol_cut_box3_eq (a0 := 0) (b0 := (dx0 : ℝ) / D_x) (a1 := 0) (b1 := (dx1 : ℝ) / D_x)
        (a2 := 0) (b2 := (dx2 : ℝ) / D_x) (L := (r : ℝ) / ((D_p : ℝ) * D_x)) (by positivity) (by positivity) (by positivity)
      simp only [sub_zero, zero_add, mul_zero] at hv
      have hfull_r : (dx0 : ℝ) / D_x + (dx1 : ℝ) / D_x + 2 * ((dx2 : ℝ) / D_x) ≤ (r : ℝ) / ((D_p : ℝ) * D_x) := by
        have hf : ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hfull
        push_cast at hf
        rw [le_div_iff₀ (by positivity)]
        have : ((dx0 : ℝ) / D_x + (dx1 : ℝ) / D_x + 2 * ((dx2 : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
            (D_p : ℝ) * dx0 + (D_p : ℝ) * dx1 + 2 * (D_p : ℝ) * dx2 := by field_simp [ne_of_gt hDx]; try ring
        linarith
      have h1 : ∀ x ∈ cell3Set .box 0 ((dx0 : ℝ) / D_x) 0 ((dx1 : ℝ) / D_x) 0 ((dx2 : ℝ) / D_x),
          ({x : Fin 3 → ℝ | x 0 + x 1 + 2 * x 2 ≤ (r : ℝ) / ((D_p : ℝ) * D_x)}).indicator (fun _ => (1 : ℝ)) x = 1 := by
        intro x hx; rw [Set.indicator_of_mem]; change x 0 + x 1 + 2 * x 2 ≤ _; linarith [hx.1.2, hx.2.1.2, hx.2.2.2]
      rw [setIntegral_congr_fun (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet h1,
          integral_cell3_eq_iter .box (by positivity) (by positivity) (by positivity) continuousOn_const] at hv
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hv
      rw [← hv]; simp only [Nat.cast_mul, (D_p3_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    · rw [Nat.cast_sub hge_nat, hsum_eq]; ring

lemma ramp3Num_eq {dx0 dx1 dx2 r : ℕ} :
    ((ramp3Num dx0 dx1 dx2 r : ℝ) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4)) =
      ramp3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 48 := by
  have hDp : (0 : ℝ) < D_p := (hDp_pos hp)
  have hDx : (0 : ℝ) < D_x := (hDx_pos hp)
  have hsc : ∀ h : ℕ, ((r - h : ℕ) : ℝ) / ((D_p : ℝ) * D_x) = max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x)) := by
    intro h
    by_cases hle : h ≤ r
    · rw [Nat.cast_sub hle, max_eq_right (sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)))]
      ring
    · push Not at hle
      rw [Nat.sub_eq_zero_of_le (le_of_lt hle), Nat.cast_zero, zero_div,
          max_eq_left (sub_nonpos.mpr (div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt hle) (by positivity)))]
  have hsum_eq : ramp3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) =
      ((ramp3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
       (ramp3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ)) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
    have hsp : ∀ h : ℕ, (max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x))) ^ 4 =
        (subPow4 r h : ℝ) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
      intro h; rw [← hsc h]; unfold subPow4; push_cast; ring
    dsimp only [ramp3SumR, ramp3Pos, ramp3Neg]
    have e0 : (r : ℝ) / ((D_p : ℝ) * D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by simp
    have e1 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e2 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e3 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e4 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e5 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e6 : (r : ℝ) / ((D_p : ℝ) * D_x) - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e7 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    rw [e7, e1, e2, e3, e4, e5, e6, hsp, hsp, hsp, hsp, hsp, hsp, hsp, e0, hsp]
    push_cast; ring
  have hvol_nn : 0 ≤ ramp3SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 48 := by
    have hv := int_ramp_box3_eq (a0 := 0) (b0 := (dx0 : ℝ) / D_x) (a1 := 0) (b1 := (dx1 : ℝ) / D_x)
      (a2 := 0) (b2 := (dx2 : ℝ) / D_x) (L := (r : ℝ) / ((D_p : ℝ) * D_x)) (by positivity) (by positivity) (by positivity)
    simp only [sub_zero, zero_add, mul_zero] at hv
    rw [← hv]
    exact setIntegral_nonneg (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet (fun x _ => le_max_left 0 _)
  have hge_nat : ramp3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r ≤ ramp3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r := by
    have hdiff_nn : (0 : ℝ) ≤ (ramp3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
        (ramp3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) := by
      rw [hsum_eq] at hvol_nn
      have hden : (0 : ℝ) < (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4 * 48 := by positivity
      have := mul_nonneg hvol_nn (le_of_lt hden)
      have hring : ((ramp3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
          (ramp3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ)) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) / 48 *
          ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4 * 48) =
          (ramp3Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) -
          (ramp3Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) r : ℝ) := by field_simp [ne_of_gt hDp, ne_of_gt hDx]
      linarith
    exact_mod_cast (sub_nonneg.mp hdiff_nn)
  unfold Buchstab4DT.ramp3Num
  by_cases hr0 : r = 0
  · subst hr0; simp only [beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div] at hsum_eq ⊢
    rw [hsum_eq]; unfold ramp3Pos ramp3Neg subPow4; simp
  · simp only [beq_iff_eq, hr0, ↓reduceIte]
    rw [Nat.cast_sub hge_nat, hsum_eq]; ring

private lemma cut4Num_eq {dx0 dx1 dx2 dx3 r : ℕ} :
    ((cut4Num dx0 dx1 dx2 dx3 r : ℝ) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4)) =
      cut4SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((dx3 : ℝ) / D_x) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 48 := by
  have hDp : (0 : ℝ) < D_p := (hDp_pos hp)
  have hDx : (0 : ℝ) < D_x := (hDx_pos hp)
  have hsc : ∀ h : ℕ, ((r - h : ℕ) : ℝ) / ((D_p : ℝ) * D_x) = max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x)) := by
    intro h
    by_cases hle : h ≤ r
    · rw [Nat.cast_sub hle, max_eq_right (sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)))]
      ring
    · push Not at hle
      rw [Nat.sub_eq_zero_of_le (le_of_lt hle), Nat.cast_zero, zero_div,
          max_eq_left (sub_nonpos.mpr (div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt hle) (by positivity)))]
  have hsum_eq : cut4SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((dx3 : ℝ) / D_x) ((r : ℝ) / ((D_p : ℝ) * D_x)) =
      ((cut4Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) -
       (cut4Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ)) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
    have hsp : ∀ h : ℕ, (max 0 ((r : ℝ) / ((D_p : ℝ) * D_x) - (h : ℝ) / ((D_p : ℝ) * D_x))) ^ 4 =
        (subPow4 r h : ℝ) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) := by
      intro h; rw [← hsc h]; unfold subPow4; push_cast; ring
    dsimp only [cut4SumR, cut4Pos, cut4Neg]
    have e0 : (r : ℝ) / ((D_p : ℝ) * D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by simp
    have e0123 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e012 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e013 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e023 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + 2 * D_p * dx2 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e123 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 + 2 * D_p * dx2 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e01 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e02 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e03 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e12 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 + 2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e13 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e23 : (r : ℝ) / ((D_p : ℝ) * D_x) - 2 * ((dx2 : ℝ) / D_x) - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((2 * D_p * dx2 + D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e1 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx0 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx0 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e2 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx1 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx1 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e3 : (r : ℝ) / ((D_p : ℝ) * D_x) - 2 * ((dx2 : ℝ) / D_x) = (r : ℝ) / ((D_p : ℝ) * D_x) - ((2 * D_p * dx2 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    have e4 : (r : ℝ) / ((D_p : ℝ) * D_x) - (dx3 : ℝ) / D_x = (r : ℝ) / ((D_p : ℝ) * D_x) - ((D_p * dx3 : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    rw [e0123, e012, e013, e023, e123, e01, e02, e03, e12, e13, e23, e1, e2, e3, e4,
        hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, hsp, e0, hsp]
    push_cast; ring
  have hvol_nn : 0 ≤ cut4SumR ((dx0 : ℝ) / D_x) ((dx1 : ℝ) / D_x) (2 * ((dx2 : ℝ) / D_x)) ((dx3 : ℝ) / D_x) ((r : ℝ) / ((D_p : ℝ) * D_x)) / 48 := by
    have hv := vol_cut_box4_eq (a0 := 0) (b0 := (dx0 : ℝ) / D_x) (a1 := 0) (b1 := (dx1 : ℝ) / D_x)
      (a2 := 0) (b2 := (dx2 : ℝ) / D_x) (a3 := 0) (b3 := (dx3 : ℝ) / D_x) (L := (r : ℝ) / ((D_p : ℝ) * D_x))
      (by positivity) (by positivity) (by positivity) (by positivity)
    simp only [sub_zero, zero_add, mul_zero] at hv
    rw [← hv]
    exact setIntegral_nonneg (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (fun x _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  have hge_nat : cut4Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r ≤
      cut4Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r := by
    have hdiff_nn : (0 : ℝ) ≤ (cut4Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) -
        (cut4Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) := by
      rw [hsum_eq] at hvol_nn
      have hden : (0 : ℝ) < (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4 * 48 := by positivity
      have := mul_nonneg hvol_nn (le_of_lt hden)
      have hring : ((cut4Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) -
          (cut4Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ)) / ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4) / 48 *
          ((D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4 * 48) =
          (cut4Pos (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) -
          (cut4Neg (D_p * dx0) (D_p * dx1) (2 * D_p * dx2) (D_p * dx3) r : ℝ) := by field_simp [ne_of_gt hDp, ne_of_gt hDx]
      linarith
    exact_mod_cast (sub_nonneg.mp hdiff_nn)
  unfold Buchstab4DT.cut4Num
  by_cases hr0 : r = 0
  · subst hr0; simp only [beq_self_eq_true, ↓reduceIte, Nat.cast_zero, zero_div] at hsum_eq ⊢
    rw [hsum_eq]; unfold cut4Pos cut4Neg subPow4; simp
  · simp only [beq_iff_eq, hr0, ↓reduceIte]
    split_ifs with hfull
    · have hv := vol_cut_box4_eq (a0 := 0) (b0 := (dx0 : ℝ) / D_x) (a1 := 0) (b1 := (dx1 : ℝ) / D_x)
        (a2 := 0) (b2 := (dx2 : ℝ) / D_x) (a3 := 0) (b3 := (dx3 : ℝ) / D_x) (L := (r : ℝ) / ((D_p : ℝ) * D_x))
        (by positivity) (by positivity) (by positivity) (by positivity)
      simp only [sub_zero, zero_add, mul_zero] at hv
      have hfull_r : (dx0 : ℝ) / D_x + (dx1 : ℝ) / D_x + 2 * ((dx2 : ℝ) / D_x) + (dx3 : ℝ) / D_x ≤ (r : ℝ) / ((D_p : ℝ) * D_x) := by
        have hf : ((D_p * dx0 + D_p * dx1 + 2 * D_p * dx2 + D_p * dx3 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hfull
        push_cast at hf
        rw [le_div_iff₀ (by positivity)]
        have : ((dx0 : ℝ) / D_x + (dx1 : ℝ) / D_x + 2 * ((dx2 : ℝ) / D_x) + (dx3 : ℝ) / D_x) * ((D_p : ℝ) * D_x) =
            (D_p : ℝ) * dx0 + (D_p : ℝ) * dx1 + 2 * (D_p : ℝ) * dx2 + (D_p : ℝ) * dx3 := by field_simp [ne_of_gt hDx]; try ring
        linarith
      have h1 : ∀ x ∈ cell4Set .box 0 ((dx0 : ℝ) / D_x) 0 ((dx1 : ℝ) / D_x) 0 ((dx2 : ℝ) / D_x) 0 ((dx3 : ℝ) / D_x),
          ({x : Fin 4 → ℝ | x 0 + x 1 + 2 * x 2 + x 3 ≤ (r : ℝ) / ((D_p : ℝ) * D_x)}).indicator (fun _ => (1 : ℝ)) x = 1 := by
        intro x hx; rw [Set.indicator_of_mem]; change x 0 + x 1 + 2 * x 2 + x 3 ≤ _; linarith [hx.1.2, hx.2.1.2, hx.2.2.1.2, hx.2.2.2.2]
      rw [setIntegral_congr_fun (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet h1] at hv
      have hvol1 : ∫ _ in cell4Set .box 0 ((dx0 : ℝ) / D_x) 0 ((dx1 : ℝ) / D_x) 0 ((dx2 : ℝ) / D_x) 0 ((dx3 : ℝ) / D_x), (1 : ℝ) =
          ((dx0 : ℝ) / D_x) * ((dx1 : ℝ) / D_x) * ((dx2 : ℝ) / D_x) * ((dx3 : ℝ) / D_x) := by
        rw [cell4Set_eq_preimage,
            volume_preserving_equivFin4_3.setIntegral_preimage_emb equivFin4_3.measurableEmbedding (fun _ => (1 : ℝ)) _]
        rw [MeasureTheory.setIntegral_prod (fun _ => (1 : ℝ))
          (continuousOn_const.integrableOn_compact (isCompact_Icc.prod (cell3Set_isCompact .box _ _ _ _ _ _)))]
        simp_rw [integral_cell3_eq_iter .box (show (0 : ℝ) ≤ (dx0 : ℝ) / D_x by positivity) (show (0 : ℝ) ≤ (dx1 : ℝ) / D_x by positivity) (show (0 : ℝ) ≤ (dx2 : ℝ) / D_x by positivity) continuousOn_const,
          intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
          MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (dx3 : ℝ) / D_x by positivity),
          intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        ring
      rw [hvol1] at hv
      rw [← hv]; simp only [Nat.cast_mul, (D_p4_cast hp)]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
    · rw [Nat.cast_sub hge_nat, hsum_eq]; ring

/-! ### Part 6: Soundness of `evalTree4`, `evalTree4Trans`, `evalTree3Mp`, `evalTree3Mm` -/

private lemma integrand4_integrableOn {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    (φ : ℝ) {knd : CellKind} {a0 b0 a1 b1 a2 b2 a3 b3 : ℝ}
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    IntegrableOn (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2))
      (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) volume := by
  set C := cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3
  have hCcomp : IsCompact C := cell4Set_isCompact knd a0 b0 a1 b1 a2 b2 a3 b3
  have hCmeas : MeasurableSet C := (cell4Set_isClosed knd a0 b0 a1 b1 a2 b2 a3 b3).measurableSet
  have hpos : ∀ x ∈ C, 0 < x 0 ∧ 0 < x 1 ∧ 0 < x 2 ∧ 0 < x 3 := by
    intro x hx; cases knd with
    | box => exact ⟨lt_of_lt_of_le ha0 hx.1.1, lt_of_lt_of_le ha1 hx.2.1.1, lt_of_lt_of_le ha2 hx.2.2.1.1, lt_of_lt_of_le ha3 hx.2.2.2.1⟩
    | tri01 => exact ⟨lt_of_lt_of_le ha0 hx.1.1, lt_of_lt_of_le ha0 hx.2.1.1, lt_of_lt_of_le ha2 hx.2.2.1.1, lt_of_lt_of_le ha3 hx.2.2.2.1.1⟩
    | tri12 => exact ⟨lt_of_lt_of_le ha0 hx.1.1, lt_of_lt_of_le ha1 hx.2.1.1, lt_of_lt_of_le ha1 hx.2.2.1.1, lt_of_lt_of_le ha3 hx.2.2.2.1.1⟩
    | simp => exact ⟨lt_of_lt_of_le ha0 hx.1.1, lt_of_lt_of_le ha0 hx.2.1.1, lt_of_lt_of_le ha0 hx.2.2.1.1, lt_of_lt_of_le ha3 hx.2.2.2.1.1⟩
  let P : Set (Fin 4 → ℝ) := {x | x 2 ≤ φ - ∑ j, x j}
  have hPm : MeasurableSet P := (isClosed_le (continuous_apply 2) (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j))).measurableSet
  have hcont_P : ContinuousOn (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) (C ∩ P) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine hω.1.comp (ContinuousOn.div (continuousOn_const.sub (continuousOn_finset_sum _ fun j _ => (continuous_apply j).continuousOn))
        (continuous_apply 2).continuousOn (fun x hx => ne_of_gt (hpos x hx.1).2.2.1)) ?_
      intro x ⟨hxC, hxP⟩; change 1 ≤ (φ - ∑ j, x j) / x 2
      exact (one_le_div (hpos x hxC).2.2.1).mpr hxP
    · exact ((continuousOn_finset_prod _ fun j _ => (continuous_apply j).continuousOn).mul (continuous_apply 2).continuousOn)
    · intro x ⟨hxC, _⟩; rcases hpos x hxC with ⟨h0, h1, h2, h3⟩; rw [Fin.prod_univ_four]; positivity
  have hmeas_ind : AEStronglyMeasurable
      (P.indicator (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)))
      (volume.restrict C) := by
    have hCP_meas : MeasurableSet (C ∩ P) := hCmeas.inter hPm
    have h_ae : AEStronglyMeasurable _ (volume.restrict (C ∩ P)) := hcont_P.aestronglyMeasurable hCP_meas
    have h_ext : AEStronglyMeasurable
        ((C ∩ P).indicator (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)))
        (volume.restrict C) := by
      have : AEStronglyMeasurable
          ((C ∩ P).indicator (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2))) volume :=
        (aestronglyMeasurable_indicator_iff hCP_meas).mpr h_ae
      exact this.restrict
    refine h_ext.congr ?_
    filter_upwards [ae_restrict_mem hCmeas] with x hxC
    by_cases hxP : x ∈ P <;> simp [hxC, hxP]
  have heq_P : ∀ x ∈ C, ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) =
      P.indicator (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) x := by
    intro x hxC
    by_cases hxP : x ∈ P
    · simp [hxP]
    · simp only [Set.indicator_of_notMem hxP]
      have hlt : (φ - ∑ j, x j) / x 2 < 1 := (div_lt_one (hpos x hxC).2.2.1).mpr (lt_of_not_ge hxP)
      rw [hω.2.2.2 _ hlt, zero_div]
  have hae_meas : AEStronglyMeasurable (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) (volume.restrict C) :=
    hmeas_ind.congr (by filter_upwards [ae_restrict_mem hCmeas] with x hxC; exact (heq_P x hxC).symm)
  have hM : IntegrableOn (fun _ : Fin 4 → ℝ => (1 / (a0 * (min a0 a1) * (min (min a0 a1) a2) ^ 2 * a3) : ℝ)) C volume :=
    continuousOn_const.integrableOn_compact hCcomp
  refine Integrable.mono' hM hae_meas ?_
  filter_upwards [ae_restrict_mem hCmeas] with x hxC
  have hnn : 0 ≤ ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) := by
    rcases hpos x hxC with ⟨h0, h1, h2, h3⟩
    exact div_nonneg (buchstab_nonneg hω _) (by rw [Fin.prod_univ_four]; positivity)
  rw [Real.norm_of_nonneg hnn]
  have h1 : ω ((φ - ∑ j, x j) / x 2) ≤ 1 := buchstab_le_one hω _
  have hle_den : a0 * (min a0 a1) * (min (min a0 a1) a2) ^ 2 * a3 ≤ (∏ j : Fin 4, x j) * x 2 := by
    rw [Fin.prod_univ_four]
    have hmin1_pos : 0 < min a0 a1 := lt_min ha0 ha1
    have hmin2_pos : 0 < min (min a0 a1) a2 := lt_min hmin1_pos ha2
    have hx0 : a0 ≤ x 0 := by cases knd <;> exact hxC.1.1
    have hx1 : min a0 a1 ≤ x 1 := by
      cases knd with
      | box => exact le_trans (min_le_right _ _) hxC.2.1.1
      | tri01 => exact le_trans (min_le_left _ _) hxC.2.1.1
      | tri12 => exact le_trans (min_le_right _ _) hxC.2.1.1
      | simp => exact le_trans (min_le_left _ _) hxC.2.1.1
    have hx2 : min (min a0 a1) a2 ≤ x 2 := by
      cases knd with
      | box => exact le_trans (min_le_right _ _) hxC.2.2.1.1
      | tri01 => exact le_trans (min_le_right _ _) hxC.2.2.1.1
      | tri12 => exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) hxC.2.2.1.1)
      | simp => exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hxC.2.2.1.1)
    have hx3 : a3 ≤ x 3 := by
      cases knd with
      | box => exact hxC.2.2.2.1
      | tri01 => exact hxC.2.2.2.1.1
      | tri12 => exact hxC.2.2.2.1.1
      | simp => exact hxC.2.2.2.1.1
    have h01 : a0 * min a0 a1 ≤ x 0 * x 1 := mul_le_mul hx0 hx1 (le_of_lt hmin1_pos) (le_trans (le_of_lt ha0) hx0)
    have h22 : (min (min a0 a1) a2) ^ 2 ≤ x 2 * x 2 := by rw [sq]; exact mul_le_mul hx2 hx2 (le_of_lt hmin2_pos) (le_trans (le_of_lt hmin2_pos) hx2)
    have h0122 : a0 * min a0 a1 * (min (min a0 a1) a2) ^ 2 ≤ (x 0 * x 1) * (x 2 * x 2) :=
      mul_le_mul h01 h22 (sq_nonneg _) (le_trans (mul_nonneg (le_of_lt ha0) (le_of_lt hmin1_pos)) h01)
    have hmul := mul_le_mul h0122 hx3 (le_of_lt ha3) (le_trans (mul_nonneg (mul_nonneg (le_of_lt ha0) (le_of_lt hmin1_pos)) (sq_nonneg _)) h0122)
    linarith
  have hden_pos : 0 < a0 * (min a0 a1) * (min (min a0 a1) a2) ^ 2 * a3 := by
    have : 0 < min a0 a1 := lt_min ha0 ha1
    have : 0 < min (min a0 a1) a2 := lt_min this ha2
    positivity
  exact div_le_div₀ (by norm_num) h1 hden_pos hle_den

lemma cell3Valid_ok {knd : CellKind} {a0 b0 a1 b1 a2 b2 : ℕ}
    (hv : cell3Valid knd a0 b0 a1 b1 a2 b2) :
    cell3Ok knd ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) := by
  rcases hv with ⟨_, h0, _, _, h1, _, _, h2, _, ht01, ht12, hts⟩
  refine ⟨div_le_div_of_nonneg_right (by exact_mod_cast h0) (le_of_lt (hDx_pos hp)),
          div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt (hDx_pos hp)),
          div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt (hDx_pos hp)), ?_⟩
  cases knd with
  | box => trivial
  | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma cell4_leaf_boundary_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {p_n : ℕ} {knd : CellKind} {n0a n0b n1a n1b n2a n2b n3a n3b : ℕ}
    (hv : cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b)
    (hzero : ¬ p_n * D_x ≤ D_p * (n0a + n1a + 2 * n2a + n3a)) :
    ∫ x in cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x)
                        ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
                        ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
      ω (((p_n : ℝ) / D_p - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (ceilDiv (S_4 * D_x * cut4Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (n3b - n3a)
          (p_n * D_x - D_p * (n0a + n1a + 2 * n2a + n3a)))
        (48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n3a) : ℝ) / S_4 := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  rcases hv with ⟨hv3, hBa3, h3le, h3C⟩
  have hok3 := cell3Valid_ok hp hv3
  rcases hv3 with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h3p : 0 < n3a := lt_of_lt_of_le (B_n_pos hp) hBa3
  set φ : ℝ := (p_n : ℝ) / D_p
  set C := cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell4Set_isClosed knd _ _ _ _ _ _ _ _).measurableSet
  have hmem : ∀ x ∈ C,
      x 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      x 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      x 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ∧
      x 3 ∈ Icc ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x) := by
    intro x hx; cases knd with
    | box => exact hx
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
  have hM_pos : 0 < ((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((n3a : ℝ) / D_x) := by
    have : (0 : ℝ) < (n0a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h0p) hDx
    have : (0 : ℝ) < (n1a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h1p) hDx
    have : (0 : ℝ) < (n2a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h2p) hDx
    have : (0 : ℝ) < (n3a : ℝ) / D_x := div_pos (Nat.cast_pos.mpr h3p) hDx
    positivity
  let M : ℝ := 1 / (((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((n3a : ℝ) / D_x))
  let Pcut : Set (Fin 4 → ℝ) := {x | x 0 + x 1 + 2 * x 2 + x 3 ≤ φ}
  have hPcut_m : MeasurableSet Pcut := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hpt : ∀ x ∈ C, ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      M * Pcut.indicator (fun _ => (1 : ℝ)) x := by
    intro x hx
    rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    have hx2p : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
    by_cases hxP : x ∈ Pcut
    · rw [Set.indicator_of_mem hxP, mul_one]
      have h1 : ω ((φ - ∑ j, x j) / x 2) ≤ 1 := buchstab_le_one hω _
      have hden : ((n0a : ℝ) / D_x) * ((n1a : ℝ) / D_x) * ((n2a : ℝ) / D_x) ^ 2 * ((n3a : ℝ) / D_x) ≤
          (∏ j : Fin 4, x j) * x 2 := by
        rw [Fin.prod_univ_four, sq]
        have h0a_nn : (0 : ℝ) ≤ (n0a : ℝ) / D_x := by positivity
        have h1a_nn : (0 : ℝ) ≤ (n1a : ℝ) / D_x := by positivity
        have h2a_nn : (0 : ℝ) ≤ (n2a : ℝ) / D_x := by positivity
        have h3a_nn : (0 : ℝ) ≤ (n3a : ℝ) / D_x := by positivity
        have h01 := mul_le_mul hx0.1 hx1.1 h1a_nn (le_trans h0a_nn hx0.1)
        have h22 := mul_le_mul hx2.1 hx2.1 h2a_nn (le_trans h2a_nn hx2.1)
        have h0122 := mul_le_mul h01 h22 (mul_nonneg h2a_nn h2a_nn) (le_trans (mul_nonneg h0a_nn h1a_nn) h01)
        have hmul := mul_le_mul h0122 hx3.1 h3a_nn (le_trans (mul_nonneg (mul_nonneg h0a_nn h1a_nn) (mul_nonneg h2a_nn h2a_nn)) h0122)
        linarith only [hmul]
      exact div_le_div₀ (by norm_num) h1 hM_pos hden
    · rw [Set.indicator_of_notMem hxP, mul_zero]
      have hlt : (φ - ∑ j, x j) / x 2 < 1 := by
        rw [div_lt_one hx2p, Fin.sum_univ_four]
        change ¬ (x 0 + x 1 + 2 * x 2 + x 3 ≤ φ) at hxP; linarith
      rw [hω.2.2.2 _ hlt, zero_div]
  have hint_ind : IntegrableOn (Pcut.indicator (fun _ => (1 : ℝ))) C volume :=
    (continuousOn_const.integrableOn_compact (cell4Set_isCompact knd _ _ _ _ _ _ _ _)).indicator hPcut_m
  have hle1 : ∫ x in C, ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      M * ∫ x in C, Pcut.indicator (fun _ => (1 : ℝ)) x := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on
      (integrand4_integrableOn hp hω φ (div_pos (Nat.cast_pos.mpr h0p) hDx)
        (div_pos (Nat.cast_pos.mpr h1p) hDx) (div_pos (Nat.cast_pos.mpr h2p) hDx)
        (div_pos (Nat.cast_pos.mpr h3p) hDx))
      (hint_ind.const_mul M) hCmeas hpt
  -- Bound ∫_C Pcut.indicator 1 ≤ (1/facDen) * ∫_{box4} Pcut.indicator 1 via Fubini + S_3 symmetry!
  have hvol_le : ∫ x in C, Pcut.indicator (fun _ => (1 : ℝ)) x ≤
      (1 / (facDen knd : ℝ)) *
        ∫ x in cell4Set .box ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                             ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
          Pcut.indicator (fun _ => (1 : ℝ)) x := by
    let S4 : Set (ℝ × (Fin 3 → ℝ)) := {p | p.2 0 + p.2 1 + 2 * p.2 2 + p.1 ≤ φ}
    have hS4m : MeasurableSet S4 := (isClosed_le (by fun_prop) continuous_const).measurableSet
    have hfun : Pcut.indicator (fun _ => (1 : ℝ)) = (S4.indicator (fun _ => (1 : ℝ))) ∘ equivFin4_3 := by
      ext x; simp [Pcut, S4, equivFin4_3_apply, Set.indicator]
    let g : ℝ → ℝ := fun s => (max 0 (φ - (n3a : ℝ) / D_x - s) - max 0 (φ - (n3b : ℝ) / D_x - s)) / 1
    have hrew_knd : ∀ k : CellKind,
        ∫ x in cell4Set k ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                          ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
          Pcut.indicator (fun _ => (1 : ℝ)) x =
        ∫ y in cell3Set k ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                          ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x), g (y 0 + y 1 + 2 * y 2) := by
      intro k
      rw [cell4Set_eq_preimage, hfun]; simp_rw [Function.comp_apply]
      rw [volume_preserving_equivFin4_3.setIntegral_preimage_emb equivFin4_3.measurableEmbedding]
      have hintk : IntegrableOn (S4.indicator (fun _ => (1 : ℝ)))
          (Icc ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x) ×ˢ
            cell3Set k ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x))
          (volume.prod volume) :=
        (continuousOn_const.integrableOn_compact (isCompact_Icc.prod (cell3Set_isCompact k _ _ _ _ _ _))).indicator hS4m
      rw [setIntegral_prod_symm' _ hintk]
      apply setIntegral_congr_fun (cell3Set_isClosed k _ _ _ _ _ _).measurableSet
      intro y _; dsimp only
      have h3r : (n3a : ℝ) / D_x ≤ (n3b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx)
      have htr : ∫ x3 in Icc ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x), S4.indicator (fun _ => (1 : ℝ)) (x3, y) =
          ∫ t in Icc (0 : ℝ) ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x),
            ({t : ℝ | 1 * t ≤ φ - (n3a : ℝ) / D_x - (y 0 + y 1 + 2 * y 2)}).indicator (fun _ => (1 : ℝ)) t := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h3r,
            MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (sub_nonneg.mpr h3r),
            show (n3a : ℝ) / D_x = 0 + (n3a : ℝ) / D_x by ring, show (n3b : ℝ) / D_x = ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x) + (n3a : ℝ) / D_x by ring,
            ← intervalIntegral.integral_comp_add_right (fun x3 => S4.indicator (fun _ => (1 : ℝ)) (x3, y)) ((n3a : ℝ) / D_x)]
        have heq_fn : (fun t : ℝ => S4.indicator (fun _ => (1 : ℝ)) (t + (n3a : ℝ) / D_x, y)) =
            ({t : ℝ | 1 * t ≤ φ - (n3a : ℝ) / D_x - (y 0 + y 1 + 2 * y 2)}).indicator (fun _ => (1 : ℝ)) := by
          ext t; simp only [Set.indicator, S4, mem_ofPred_eq]; split_ifs with h' h'' <;> try rfl
          · exfalso; apply h''; linarith
          · exfalso; apply h'; linarith
        rw [heq_fn]; congr 1 <;> ring
      rw [htr, integral_ind_le_sub (by norm_num : (0 : ℝ) < 1) (sub_nonneg.mpr h3r)]
      dsimp only [g]; ring_nf
    rw [hrew_knd knd, hrew_knd .box]
    refine s3_antitone_le knd hok3 ?_ ?_ ?_
    · intro s; dsimp only [g]
      have h3r : (n3a : ℝ) / D_x ≤ (n3b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx)
      have : max 0 (φ - (n3b : ℝ) / D_x - s) ≤ max 0 (φ - (n3a : ℝ) / D_x - s) := max_le_max_left 0 (by linarith)
      linarith
    · intro s1 s2 hs; dsimp only [g]
      have h3r : (n3a : ℝ) / D_x ≤ (n3b : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx)
      have hdif : ∀ u v : ℝ, u ≤ v → max 0 (φ - (n3a : ℝ) / D_x - v) - max 0 (φ - (n3b : ℝ) / D_x - v) ≤
          max 0 (φ - (n3a : ℝ) / D_x - u) - max 0 (φ - (n3b : ℝ) / D_x - u) := by
        intro u v huv
        by_cases h1 : 0 ≤ φ - (n3b : ℝ) / D_x - v
        · rw [max_eq_right h1, max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
        · push Not at h1; rw [max_eq_left (le_of_lt h1)]
          by_cases h2 : φ - (n3b : ℝ) / D_x - u ≤ 0
          · rw [max_eq_left h2]; linarith [max_le_max_left 0 (show φ - (n3a : ℝ) / D_x - v ≤ φ - (n3a : ℝ) / D_x - u by linarith)]
          · push Not at h2; rw [max_eq_right (le_of_lt h2), max_eq_right (by linarith : 0 ≤ φ - (n3a : ℝ) / D_x - u)]
            have : max 0 (φ - (n3a : ℝ) / D_x - v) ≤ (n3b : ℝ) / D_x - (n3a : ℝ) / D_x :=
              max_le (by linarith) (by linarith)
            linarith
      linarith [hdif s1 s2 hs]
    · exact (Continuous.continuousOn (by dsimp only [g]; fun_prop)).integrableOn_compact
        (cell3Set_isCompact .box _ _ _ _ _ _)
  rw [vol_cut_box4_eq (div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx))
      (div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx))
      (div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx))
      (div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx))] at hvol_le
  have hr_sub : D_p * (n0a + n1a + 2 * n2a + n3a) ≤ p_n * D_x := by omega
  have hR_eq : φ - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + (n3a : ℝ) / D_x) =
      ((p_n * D_x - D_p * (n0a + n1a + 2 * n2a + n3a) : ℕ) : ℝ) / ((D_p : ℝ) * D_x) := by
    rw [Nat.cast_sub hr_sub]; dsimp only [φ]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
  have hdx_eq : ∀ a b : ℕ, a ≤ b → (b : ℝ) / D_x - (a : ℝ) / D_x = ((b - a : ℕ) : ℝ) / D_x := by
    intro a b hab; rw [Nat.cast_sub hab]; ring
  rw [hR_eq, hdx_eq n0a n0b h0le, hdx_eq n1a n1b h1le, hdx_eq n2a n2b h2le, hdx_eq n3a n3b h3le, ← cut4Num_eq hp] at hvol_le
  have hM_nn : 0 ≤ M := by positivity
  have hstep := le_trans hle1 (mul_le_mul_of_nonneg_left hvol_le hM_nn)
  refine le_trans hstep ?_
  set vc := cut4Num (n0b - n0a) (n1b - n1a) (n2b - n2a) (n3b - n3a) (p_n * D_x - D_p * (n0a + n1a + 2 * n2a + n3a))
  have hden_nat : 0 < 48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n3a :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by cases knd <;> simp [facDen])) (hDp4_nat_pos hp)) h0p) h1p) h2p) h2p) h3p
  have hcd : ((S_4 * D_x * vc : ℕ) : ℝ) ≤
      ((48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n3a : ℕ) : ℝ) *
      (ceilDiv (S_4 * D_x * vc) (48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n3a) : ℝ) := by
    exact_mod_cast le_mul_ceilDiv hden_nat
  have hfd_pos : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
  rw [le_div_iff₀ (hS4_pos hp)]
  have hLHS : M * ((1 / (facDen knd : ℝ)) * ((vc : ℝ) / (48 * (D_p : ℝ) ^ 4 * (D_x : ℝ) ^ 4))) * S_4 =
      ((S_4 * D_x * vc : ℕ) : ℝ) / ((48 * facDen knd * D_p4 * n0a * n1a * n2a * n2a * n3a : ℕ) : ℝ) := by
    dsimp only [M]; simp only [Nat.cast_mul, (D_p4_cast hp)]
    have h0r : (0 : ℝ) < n0a := Nat.cast_pos.mpr h0p
    have h1r : (0 : ℝ) < n1a := Nat.cast_pos.mpr h1p
    have h2r : (0 : ℝ) < n2a := Nat.cast_pos.mpr h2p
    have h3r : (0 : ℝ) < n3a := Nat.cast_pos.mpr h3p
    have hgen : ∀ (x0 x1 x2 x3 Dx Dp fd v S4 : ℝ), Dx ≠ 0 → Dp ≠ 0 → fd ≠ 0 → x0 ≠ 0 → x1 ≠ 0 → x2 ≠ 0 → x3 ≠ 0 →
        (1 / (x0 / Dx * (x1 / Dx) * (x2 / Dx) ^ 2 * (x3 / Dx))) * (1 / fd * (v / (48 * Dp ^ 4 * Dx ^ 4))) * S4 =
        (S4 * Dx * v) / (48 * fd * Dp ^ 4 * x0 * x1 * x2 * x2 * x3) := by
      intro x0 x1 x2 x3 Dx Dp fd v S4 h1 h2 h3 h4 h5 h6 h7; field_simp [h1, h2, h3, h4, h5, h6, h7]
    exact hgen n0a n1a n2a n3a D_x D_p (facDen knd) vc S_4 (ne_of_gt hDx) (ne_of_gt hDp) (ne_of_gt hfd_pos) (ne_of_gt h0r) (ne_of_gt h1r) (ne_of_gt h2r) (ne_of_gt h3r)
  rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith

lemma cell4_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {p_n : ℕ} (hp_top : (p_n : ℝ) / D_p ≤ 5 * A_R + B_R)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b n3a n3b : ℕ}
    (hv : cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b) :
    ∫ x in cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x)
                        ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
                        ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
      ω (((p_n : ℝ) / D_p - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4Leaf p_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / S_4 := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  rcases hv with ⟨hv3, hBa3, h3le, h3C⟩
  have hok3 := cell3Valid_ok hp hv3
  rcases hv3 with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h3p : 0 < n3a := lt_of_lt_of_le (B_n_pos hp) hBa3
  set φ : ℝ := (p_n : ℝ) / D_p
  set C := cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x)
  have hmem : ∀ x ∈ C,
      x 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      x 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      x 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ∧
      x 3 ∈ Icc ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x) := by
    intro x hx; cases knd with
    | box => exact hx
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
  have hCmeas : MeasurableSet C := (cell4Set_isClosed knd _ _ _ _ _ _ _ _).measurableSet
  have hu_le2 : ∀ x ∈ C, (φ - ∑ j, x j) / x 2 ≤ 2 := by
    intro x hx
    rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    have hA0r : A_R ≤ x 0 := le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)) hx0.1
    have hA1r : A_R ≤ x 1 := le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)) hx1.1
    have hA2r : A_R ≤ x 2 := le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)) hx2.1
    have hB3r : B_R ≤ x 3 := le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hBa3) (le_of_lt hDx)) hx3.1
    have hx2p : 0 < x 2 := lt_of_lt_of_le (hA_pos hp) hA2r
    rw [div_le_iff₀ hx2p, Fin.sum_univ_four]
    linarith [hp_top]
  unfold Buchstab4DT.eval4Leaf; dsimp only
  split_ifs with hzero hint_case
  · -- Case 1: p_sc ≤ s_min -> integrand = 0 a.e. (only x0+x1+2*x2+x3 = φ can have u = 1, measure 0!)
    have hle_r : φ ≤ (n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + (n3a : ℝ) / D_x := by
      have h' : ((p_n * D_x : ℕ) : ℝ) ≤ ((D_p * (n0a + n1a + 2 * n2a + n3a) : ℕ) : ℝ) := by exact_mod_cast hzero
      push_cast at h'
      have : (φ - ((n0a : ℝ) / D_x + (n1a : ℝ) / D_x + 2 * ((n2a : ℝ) / D_x) + (n3a : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
          (p_n : ℝ) * D_x - (D_p : ℝ) * ((n0a : ℝ) + n1a + 2 * n2a + n3a) := by
        dsimp only [φ]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      nlinarith [mul_pos hDp hDx]
    have hae_zero : ∀ᵐ x ∂volume, x ∈ C → ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) = 0 := by
      have hmeas0 : volume {x : Fin 4 → ℝ | x 3 = (n3a : ℝ) / D_x} = 0 := by
        have hpre : {x : Fin 4 → ℝ | x 3 = (n3a : ℝ) / D_x} = equivFin4_3 ⁻¹' ({(n3a : ℝ) / D_x} ×ˢ Set.univ) := by
          ext x; simp [equivFin4_3_apply]
        rw [hpre, volume_preserving_equivFin4_3.measure_preimage
          (MeasurableSet.prod (measurableSet_singleton _) MeasurableSet.univ).nullMeasurableSet,
          Measure.prod_prod, Real.volume_singleton, zero_mul]
      filter_upwards [compl_mem_ae_iff.mpr hmeas0] with x hne hxC
      rcases hmem x hxC with ⟨hx0, hx1, hx2, hx3⟩
      have hx3_gt : (n3a : ℝ) / D_x < x 3 := lt_of_le_of_ne hx3.1 (Ne.symm hne)
      have hx2p : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
      have hlt : (φ - ∑ j, x j) / x 2 < 1 := by
        rw [div_lt_one hx2p, Fin.sum_univ_four]
        linarith [hx0.1, hx1.1, hx2.1]
      rw [hω.2.2.2 _ hlt, zero_div]
    rw [setIntegral_congr_ae hCmeas hae_zero, integral_zero]; simp
  · -- Case 2: s_max ≤ p_sc -> interior cell, 1 ≤ u ≤ 2 everywhere -> 4D Hermite-Hadamard!
    have hphi_ge : (n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + (n3b : ℝ) / D_x ≤ φ := by
      have h' : ((D_p * (n0b + n1b + 2 * n2b + n3b) : ℕ) : ℝ) ≤ ((p_n * D_x : ℕ) : ℝ) := by exact_mod_cast hint_case
      push_cast at h'
      have : (φ - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + 2 * ((n2b : ℝ) / D_x) + (n3b : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
          (p_n : ℝ) * D_x - (D_p : ℝ) * ((n0b : ℝ) + n1b + 2 * n2b + n3b) := by
        dsimp only [φ]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      nlinarith [mul_pos hDp hDx]
    let f : (Fin 4 → ℝ) → ℝ := fun x => (x 0 * x 1 * x 2 * x 3 * (φ - (x 0 + x 1 + x 2 + x 3)))⁻¹
    have hcongr : ∀ x ∈ C, ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) = f x := by
      intro x hx
      rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
      have hx2p : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
      have hu1 : 1 ≤ (φ - ∑ j, x j) / x 2 := by
        rw [one_le_div hx2p, Fin.sum_univ_four]; linarith [hx0.2, hx1.2, hx2.2, hx3.2]
      rw [hω.2.1 _ hu1 (hu_le2 x hx), Fin.sum_univ_four, Fin.prod_univ_four]
      dsimp only [f]
      have hrem : 0 < φ - (x 0 + x 1 + x 2 + x 3) := by linarith [hx0.2, hx1.2, hx2.2, hx3.2]
      have h0' : 0 < x 0 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
      have h1' : 0 < x 1 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
      have h3' : 0 < x 3 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
      field_simp [ne_of_gt h0', ne_of_gt h1', ne_of_gt hx2p, ne_of_gt h3', ne_of_gt hrem]
    rw [setIntegral_congr_fun hCmeas hcongr]
    have hconv : ConvexOn ℝ C f := by
      let L : Fin 5 → (Fin 4 → ℝ) → ℝ :=
        ![fun x => x 0, fun x => x 1, fun x => x 2, fun x => x 3, fun x => φ - (x 0 + x 1 + x 2 + x 3)]
      have hfeq : f = fun x => (∏ i : Fin 5, L i x)⁻¹ := by
        ext x; dsimp only [f, L]; rw [Fin.prod_univ_five]; simp
      rw [hfeq]
      refine convexOn_inv_prod (cell4Set_convex knd _ _ _ _ _ _ _ _) L ?_ ?_
      · intro i x _ y _ a b _ _ hab; have ha1 : a = 1 - b := by linarith
        fin_cases i <;> simp [L, smul_eq_mul] <;> (rw [ha1]; ring)
      · intro i x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
        have h2' : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
        fin_cases i <;> dsimp only [L]
        · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
        · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
        · exact h2'
        · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
        · change 0 < φ - (x 0 + x 1 + x 2 + x 3); linarith [hx0.2, hx1.2, hx2.2, hx3.2]
    have hcont : ContinuousOn f C := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
      have h0' : 0 < x 0 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
      have h1' : 0 < x 1 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
      have h2' : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
      have h3' : 0 < x 3 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
      have hrem : 0 < φ - (x 0 + x 1 + x 2 + x 3) := by linarith [hx0.2, hx1.2, hx2.2, hx3.2]
      positivity
    have hhh := hh_cell4 knd hok3 (div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx)) hconv hcont
    -- Bound each vertex value by ceilDiv!
    have hv_le : ∀ a0 a1 a2 a3 : ℕ, 0 < a0 → 0 < a1 → 0 < a2 → 0 < a3 →
        a0 ≤ n0b → a1 ≤ n1b → a2 ≤ n2b → a3 ≤ n3b →
        f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (a3 : ℝ) / D_x] ≤
          (ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3))) : ℝ) / S_v := by
      intro a0 a1 a2 a3 ha0 ha1 ha2 ha3 hle0 hle1 hle2 hle3
      have hrem_pos_nat : 0 < p_n * D_x - D_p * (a0 + a1 + a2 + a3) := by
        have hsum_le : a0 + a1 + a2 + a3 < n0b + n1b + 2 * n2b + n3b := by omega
        have hDp_p : 0 < D_p := (hDp_nat_pos hp)
        have : D_p * (a0 + a1 + a2 + a3) < D_p * (n0b + n1b + 2 * n2b + n3b) := Nat.mul_lt_mul_of_pos_left hsum_le hDp_p
        omega
      have hden_pos : 0 < a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3)) := by positivity
      have hcd : ((S_v * D_x5 * D_p : ℕ) : ℝ) ≤
          ((a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3)) : ℕ) : ℝ) *
          (ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3))) : ℝ) := by
        exact_mod_cast le_mul_ceilDiv (a := S_v * D_x5 * D_p) hden_pos
      have hsub_nat : D_p * (a0 + a1 + a2 + a3) ≤ p_n * D_x := by omega
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hsub_nat] at hcd
      dsimp only [f]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hden_r : 0 < ((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x) *
          (φ - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x + (a3 : ℝ) / D_x)) := by
        have hrem_r : 0 < φ - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x + (a3 : ℝ) / D_x) := by
          have : ((D_p * (a0 + a1 + a2 + a3) : ℕ) : ℝ) < ((p_n * D_x : ℕ) : ℝ) := by exact_mod_cast (show D_p * (a0 + a1 + a2 + a3) < p_n * D_x by omega)
          push_cast at this
          have hmul : (φ - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x + (a3 : ℝ) / D_x)) * ((D_p : ℝ) * D_x) =
              (p_n : ℝ) * D_x - (D_p : ℝ) * ((a0 : ℝ) + a1 + a2 + a3) := by dsimp only [φ]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
          nlinarith [mul_pos hDp hDx]
        positivity
      rw [inv_eq_one_div, div_le_div_iff₀ hden_r (hSv_pos hp)]
      have hlhs : (1 : ℝ) * (S_v : ℝ) * ((D_x : ℝ) ^ 5 * D_p) = ((S_v * D_x5 * D_p : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, (D_x5_cast hp)]; ring
      have hrhs : (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x) *
          (φ - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x + (a3 : ℝ) / D_x))) * ((D_x : ℝ) ^ 5 * D_p) =
          (a0 : ℝ) * a1 * a2 * a3 * ((p_n : ℝ) * D_x - (D_p : ℝ) * ((a0 : ℝ) + a1 + a2 + a3)) := by
        dsimp only [φ]; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
      have hpos_m : (0 : ℝ) < (D_x : ℝ) ^ 5 * D_p := by positivity
      rw [← mul_le_mul_iff_left₀ hpos_m, hlhs]
      have hr2 : (ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3))) : ℝ) *
          (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x) *
            (φ - ((a0 : ℝ) / D_x + (a1 : ℝ) / D_x + (a2 : ℝ) / D_x + (a3 : ℝ) / D_x))) * ((D_x : ℝ) ^ 5 * D_p) =
          ((a0 : ℝ) * a1 * a2 * a3 * ((p_n : ℝ) * D_x - (D_p : ℝ) * ((a0 : ℝ) + a1 + a2 + a3))) *
          (ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * a3 * (p_n * D_x - D_p * (a0 + a1 + a2 + a3))) : ℝ) := by
        rw [mul_assoc, hrhs, mul_comm]
      rw [hr2]; push_cast at hcd ⊢; exact hcd
    have hsum_le :
        sumVerts3R (fun y => f ![y 0, y 1, y 2, (n3a : ℝ) / D_x] + f ![y 0, y 1, y 2, (n3b : ℝ) / D_x])
          knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ≤
        (sumVerts3 (fun a0 a1 a2 =>
          ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3a * (p_n * D_x - D_p * (a0 + a1 + a2 + n3a))) +
          ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3b * (p_n * D_x - D_p * (a0 + a1 + a2 + n3b))))
          knd n0a n0b n1a n1b n2a n2b : ℝ) / S_v := by
      have hp3 : ∀ a0 a1 a2 : ℕ, 0 < a0 → 0 < a1 → 0 < a2 → a0 ≤ n0b → a1 ≤ n1b → a2 ≤ n2b →
          f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (n3a : ℝ) / D_x] +
          f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (n3b : ℝ) / D_x] ≤
          ((ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3a * (p_n * D_x - D_p * (a0 + a1 + a2 + n3a))) +
            ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3b * (p_n * D_x - D_p * (a0 + a1 + a2 + n3b))) : ℕ) : ℝ) / S_v := by
        intro a0 a1 a2 ha0 ha1 ha2 hle0 hle1 hle2
        have h1 := hv_le a0 a1 a2 n3a ha0 ha1 ha2 h3p hle0 hle1 hle2 h3le
        have h2 := hv_le a0 a1 a2 n3b ha0 ha1 ha2 (lt_of_lt_of_le h3p h3le) hle0 hle1 hle2 (le_refl _)
        rw [Nat.cast_add, add_div]; linarith only [h1, h2]
      have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
      have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
      have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
      refine sumVerts3R_le knd ht01 ht12 hts (fun a0 a1 a2 ha0 ha1 ha2 => ?_)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact hp3 a0 a1 a2 (by rcases ha0 with rfl | rfl <;> assumption) (by rcases ha1 with rfl | rfl <;> assumption)
        (by rcases ha2 with rfl | rfl <;> assumption) (by rcases ha0 with rfl | rfl <;> omega)
        (by rcases ha1 with rfl | rfl <;> omega) (by rcases ha2 with rfl | rfl <;> omega)
    have hvol_nn : 0 ≤ ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
        ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) * ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x) /
        ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ))) := by
      have : (0 : ℝ) ≤ (n0b : ℝ) / D_x - (n0a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n1b : ℝ) / D_x - (n1a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n2b : ℝ) / D_x - (n2a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n3b : ℝ) / D_x - (n3a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx))
      have : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
      have : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
      positivity
    have hstep := le_trans hhh (mul_le_mul_of_nonneg_left hsum_le hvol_nn)
    refine le_trans hstep ?_
    set sv := sumVerts3 (fun a0 a1 a2 =>
      ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3a * (p_n * D_x - D_p * (a0 + a1 + a2 + n3a))) +
      ceilDiv (S_v * D_x5 * D_p) (a0 * a1 * a2 * n3b * (p_n * D_x - D_p * (a0 + a1 + a2 + n3b))))
      knd n0a n0b n1a n1b n2a n2b
    have hden_nat : 0 < facDen knd * (2 * nVerts3 knd) * D_x4 * S_v :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by cases knd <;> simp [facDen]) (Nat.mul_pos (by decide) (by cases knd <;> simp [nVerts3]))) (hDx4_nat_pos hp)) (hSv_nat_pos hp)
    have hcd : ((S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv : ℕ) : ℝ) ≤
        ((facDen knd * (2 * nVerts3 knd) * D_x4 * S_v : ℕ) : ℝ) *
        (ceilDiv (S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv)
          (facDen knd * (2 * nVerts3 knd) * D_x4 * S_v) : ℝ) := by
      exact_mod_cast le_mul_ceilDiv hden_nat
    have hsub0 : ((n0b - n0a : ℕ) : ℝ) = (n0b : ℝ) - n0a := Nat.cast_sub h0le
    have hsub1 : ((n1b - n1a : ℕ) : ℝ) = (n1b : ℝ) - n1a := Nat.cast_sub h1le
    have hsub2 : ((n2b - n2a : ℕ) : ℝ) = (n2b : ℝ) - n2a := Nat.cast_sub h2le
    have hsub3 : ((n3b - n3a : ℕ) : ℝ) = (n3b : ℝ) - n3a := Nat.cast_sub h3le
    have hfd_pos : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
    have hnv_pos : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
    rw [le_div_iff₀ (hS4_pos hp)]
    have hLHS : ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
        ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) * ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x) /
        ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ))) * ((sv : ℝ) / S_v) * S_4 =
        ((S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv : ℕ) : ℝ) /
        ((facDen knd * (2 * nVerts3 knd) * D_x4 * S_v : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, (D_x4_cast hp)]; rw [hsub0, hsub1, hsub2, hsub3]
      have hgen : ∀ (x0 x1 x2 x3 s fd nv Dx Sv S4 : ℝ), Dx ≠ 0 → fd ≠ 0 → nv ≠ 0 → Sv ≠ 0 →
          (x0 / Dx) * (x1 / Dx) * (x2 / Dx) * (x3 / Dx) / (fd * (2 * nv)) * (s / Sv) * S4 =
          (S4 * x0 * x1 * x2 * x3 * s) / (fd * (2 * nv) * Dx ^ 4 * Sv) := by
        intro x0 x1 x2 x3 s fd nv Dx Sv S4 h1 h2 h3 h4; field_simp [h1, h2, h3, h4]
      rw [← sub_div, ← sub_div, ← sub_div, ← sub_div]
      exact hgen ((n0b : ℝ) - n0a) ((n1b : ℝ) - n1a) ((n2b : ℝ) - n2a) ((n3b : ℝ) - n3a)
        sv (facDen knd) (nVerts3 knd) D_x S_v S_4 (ne_of_gt hDx) (ne_of_gt hfd_pos) (ne_of_gt hnv_pos) (ne_of_gt (hSv_pos hp))
    rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]
    linarith
  · exact cell4_leaf_boundary_sound hp hω ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩, hBa3, h3le, h3C⟩ hzero

lemma cell4_trans_leaf_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {pa_n : ℕ} {φ : ℝ} (hφ_lo : (pa_n : ℝ) / D_p ≤ φ)
    (hpa_ge : D_p * (4 * B_n + C_n) ≤ pa_n * D_x)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b n3a n3b : ℕ}
    (hv : cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b) :
    ∫ x in cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x)
                        ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)
                        ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
      ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4TransLeaf pa_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / S_4 := by
  have hDx := (hDx_pos hp)
  have hDp := (hDp_pos hp)
  rcases hv with ⟨hv3, hBa3, h3le, h3C⟩
  have hok3 := cell3Valid_ok hp hv3
  rcases hv3 with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  have h3p : 0 < n3a := lt_of_lt_of_le (B_n_pos hp) hBa3
  have h0bp : 0 < n0b := lt_of_lt_of_le h0p h0le
  have h1bp : 0 < n1b := lt_of_lt_of_le h1p h1le
  have h2bp : 0 < n2b := lt_of_lt_of_le h2p h2le
  have h3bp : 0 < n3b := lt_of_lt_of_le h3p h3le
  set C := cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                        ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x)
  have hCmeas : MeasurableSet C := (cell4Set_isClosed knd _ _ _ _ _ _ _ _).measurableSet
  have hmem : ∀ x ∈ C,
      x 0 ∈ Icc ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ∧
      x 1 ∈ Icc ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ∧
      x 2 ∈ Icc ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ∧
      x 3 ∈ Icc ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x) := by
    intro x hx; cases knd with
    | box => exact hx
    | tri01 => rcases ht01 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | tri12 => rcases ht12 rfl with ⟨rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
    | simp => rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
  set num_u := pa_n * D_x - D_p * (n0b + n1b + n2b + n3b)
  set den_u := D_p * n2b
  have hden_le_num : den_u ≤ num_u := by
    have hsum : n0b + n1b + 2 * n2b + n3b ≤ 4 * B_n + C_n := by omega
    have h1 : D_p * (n0b + n1b + 2 * n2b + n3b) ≤ pa_n * D_x := le_trans (Nat.mul_le_mul_left D_p hsum) hpa_ge
    have hsplit : D_p * (n0b + n1b + 2 * n2b + n3b) = D_p * (n0b + n1b + n2b + n3b) + D_p * n2b := by ring
    dsimp only [num_u, den_u]; omega
  have hden_pos_nat : 0 < den_u := Nat.mul_pos ((hDp_nat_pos hp)) h2bp
  have hden_pos_r : (0 : ℝ) < den_u := by exact_mod_cast hden_pos_nat
  have hnum_pos : 0 < num_u := lt_of_lt_of_le (Nat.mul_pos ((hDp_nat_pos hp)) h2bp) hden_le_num
  have hsub_u : D_p * (n0b + n1b + n2b + n3b) ≤ pa_n * D_x := by
    have hsum : n0b + n1b + n2b + n3b ≤ 4 * B_n + C_n := by omega
    exact le_trans (Nat.mul_le_mul_left D_p hsum) hpa_ge
  set om_ub := if 2 * num_u ≤ 3 * den_u then ceilDiv (S_v * den_u) num_u else ceilDiv (2 * S_v) 3
  have hom_bound : ∀ x ∈ C, ω ((φ - ∑ j, x j) / x 2) ≤ (om_ub : ℝ) / S_v := by
    intro x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    have hx2p : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
    have hu_ge : (num_u : ℝ) / (den_u : ℝ) ≤ (φ - ∑ j, x j) / x 2 := by
      have hnum_r : (num_u : ℝ) / ((D_p : ℝ) * D_x) ≤ φ - ∑ j, x j := by
        rw [Fin.sum_univ_four]
        have heq : (num_u : ℝ) / ((D_p : ℝ) * D_x) = (pa_n : ℝ) / D_p - ((n0b : ℝ) / D_x + (n1b : ℝ) / D_x + (n2b : ℝ) / D_x + (n3b : ℝ) / D_x) := by
          dsimp only [num_u]; rw [Nat.cast_sub hsub_u]; push_cast; field_simp [ne_of_gt hDp, ne_of_gt hDx]; try ring
        rw [heq]; linarith [hφ_lo, hx0.2, hx1.2, hx2.2, hx3.2]
      have hden_r : x 2 ≤ (den_u : ℝ) / ((D_p : ℝ) * D_x) := by
        have heq : (den_u : ℝ) / ((D_p : ℝ) * D_x) = (n2b : ℝ) / D_x := by
          dsimp only [den_u]; push_cast; field_simp [ne_of_gt hDp]
        rw [heq]; exact hx2.2
      have heq_div : (num_u : ℝ) / (den_u : ℝ) = ((num_u : ℝ) / ((D_p : ℝ) * D_x)) / ((den_u : ℝ) / ((D_p : ℝ) * D_x)) := by
        field_simp [ne_of_gt hDp, ne_of_gt hDx]
      rw [heq_div]
      exact div_le_div₀ (le_trans (by positivity : (0 : ℝ) ≤ (num_u : ℝ) / ((D_p : ℝ) * D_x)) hnum_r) hnum_r hx2p hden_r
    have hu1 : 1 ≤ (φ - ∑ j, x j) / x 2 := le_trans ((one_le_div hden_pos_r).mpr (by exact_mod_cast hden_le_num)) hu_ge
    have hmx := buchstab_le_max_inv_two_thirds hω hu1
    have hinv_le : 1 / ((φ - ∑ j, x j) / x 2) ≤ (den_u : ℝ) / (num_u : ℝ) := by
      have h1 := one_div_le_one_div_of_le (div_pos (by exact_mod_cast hnum_pos) hden_pos_r) hu_ge
      simpa only [one_div_div] using h1
    have hmx2 : ω ((φ - ∑ j, x j) / x 2) ≤ max ((den_u : ℝ) / (num_u : ℝ)) (2 / 3) :=
      le_trans hmx (max_le_max_right _ hinv_le)
    refine le_trans hmx2 ?_
    dsimp only [om_ub]; split_ifs with hif
    · have hge : (2 : ℝ) / 3 ≤ (den_u : ℝ) / (num_u : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast hnum_pos)]
        have h' : ((2 * num_u : ℕ) : ℝ) ≤ ((3 * den_u : ℕ) : ℝ) := by exact_mod_cast hif
        push_cast at h'; linarith
      rw [max_eq_left hge, div_le_div_iff₀ (by exact_mod_cast hnum_pos) (hSv_pos hp)]
      have hcd := le_mul_ceilDiv (a := S_v * den_u) hnum_pos
      have : ((S_v * den_u : ℕ) : ℝ) ≤ ((num_u * ceilDiv (S_v * den_u) num_u : ℕ) : ℝ) := by exact_mod_cast hcd
      push_cast at this; linarith
    · push Not at hif
      have hle : (den_u : ℝ) / (num_u : ℝ) ≤ (2 : ℝ) / 3 := by
        rw [div_le_div_iff₀ (by exact_mod_cast hnum_pos) (by norm_num)]
        have h' : ((3 * den_u : ℕ) : ℝ) ≤ ((2 * num_u : ℕ) : ℝ) := by exact_mod_cast le_of_lt hif
        push_cast at h'; linarith
      rw [max_eq_right hle, div_le_div_iff₀ (by norm_num) (hSv_pos hp)]
      have hcd := le_mul_ceilDiv (a := 2 * S_v) (by omega : 0 < 3)
      have : ((2 * S_v : ℕ) : ℝ) ≤ ((3 * ceilDiv (2 * S_v) 3 : ℕ) : ℝ) := by exact_mod_cast hcd
      push_cast at this; linarith
  let f : (Fin 4 → ℝ) → ℝ := fun x => (x 0 * x 1 * x 2 * x 2 * x 3)⁻¹
  have hconv : ConvexOn ℝ C f := by
    let L : Fin 5 → (Fin 4 → ℝ) → ℝ := ![fun x => x 0, fun x => x 1, fun x => x 2, fun x => x 2, fun x => x 3]
    have hfeq : f = fun x => (∏ i : Fin 5, L i x)⁻¹ := by ext x; dsimp only [f, L]; rw [Fin.prod_univ_five]; simp
    rw [hfeq]
    refine convexOn_inv_prod (cell4Set_convex knd _ _ _ _ _ _ _ _) L
      (fun i _ _ _ _ _ _ _ _ _ => by fin_cases i <;> simp [L, smul_eq_mul]) ?_
    intro i x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    fin_cases i <;> dsimp only [L]
    · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
    · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
    · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
    · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
    · exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
  have hcont : ContinuousOn f C := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    have : 0 < x 0 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
    have : 0 < x 1 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
    have : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
    have : 0 < x 3 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
    positivity
  have hle1 : ∫ x in C, ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      ((om_ub : ℝ) / S_v) * ∫ x in C, f x := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      (integrand4_integrableOn hp hω φ (div_pos (Nat.cast_pos.mpr h0p) hDx)
        (div_pos (Nat.cast_pos.mpr h1p) hDx) (div_pos (Nat.cast_pos.mpr h2p) hDx)
        (div_pos (Nat.cast_pos.mpr h3p) hDx))
      ((hcont.integrableOn_compact (cell4Set_isCompact knd _ _ _ _ _ _ _ _)).const_mul _) hCmeas ?_
    intro x hx; rcases hmem x hx with ⟨hx0, hx1, hx2, hx3⟩
    have hden_pos : 0 < (∏ j : Fin 4, x j) * x 2 := by
      rw [Fin.prod_univ_four]
      have : 0 < x 0 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h0p) hDx) hx0.1
      have : 0 < x 1 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h1p) hDx) hx1.1
      have : 0 < x 2 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h2p) hDx) hx2.1
      have : 0 < x 3 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr h3p) hDx) hx3.1
      positivity
    have heq_f : f x = 1 / ((∏ j : Fin 4, x j) * x 2) := by dsimp only [f]; rw [Fin.prod_univ_four, one_div]; congr 1; ring
    rw [heq_f, mul_one_div]
    exact div_le_div_of_nonneg_right (hom_bound x hx) (le_of_lt hden_pos)
  have hhh := hh_cell4 knd hok3 (div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx)) hconv hcont
  have hv_le : ∀ a0 a1 a2 a3 : ℕ, 0 < a0 → 0 < a1 → 0 < a2 → 0 < a3 →
      f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (a3 : ℝ) / D_x] ≤
        (ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * a3) : ℝ) / S_v := by
    intro a0 a1 a2 a3 ha0 ha1 ha2 ha3
    have hcd : ((S_v * D_x5 : ℕ) : ℝ) ≤ ((a0 * a1 * a2 * a2 * a3 : ℕ) : ℝ) * (ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * a3) : ℝ) := by
      exact_mod_cast le_mul_ceilDiv (a := S_v * D_x5) (by positivity : 0 < a0 * a1 * a2 * a2 * a3)
    dsimp only [f]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have hden_r : 0 < ((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x) := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ hden_r (hSv_pos hp)]
    have hlhs : (1 : ℝ) * S_v * (D_x : ℝ) ^ 5 = ((S_v * D_x5 : ℕ) : ℝ) := by rw [Nat.cast_mul, (D_x5_cast hp)]; ring
    have hrhs : (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x)) * (D_x : ℝ) ^ 5 =
        ((a0 * a1 * a2 * a2 * a3 : ℕ) : ℝ) := by push_cast; field_simp [ne_of_gt hDx]
    have hpm : (0 : ℝ) < (D_x : ℝ) ^ 5 := by positivity
    rw [← mul_le_mul_iff_left₀ hpm, hlhs]
    have hr2 : (ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * a3) : ℝ) * (((a0 : ℝ) / D_x) * ((a1 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a2 : ℝ) / D_x) * ((a3 : ℝ) / D_x)) * (D_x : ℝ) ^ 5 =
        ((a0 * a1 * a2 * a2 * a3 : ℕ) : ℝ) * (ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * a3) : ℝ) := by rw [mul_assoc, hrhs, mul_comm]
    rw [hr2]; exact hcd
  set sv := sumVerts3 (fun a0 a1 a2 =>
    ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * n3a) + ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * n3b))
    knd n0a n0b n1a n1b n2a n2b
  have hsum_le :
      sumVerts3R (fun y => f ![y 0, y 1, y 2, (n3a : ℝ) / D_x] + f ![y 0, y 1, y 2, (n3b : ℝ) / D_x])
        knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ≤
      (sv : ℝ) / S_v := by
    have hp3 : ∀ a0 a1 a2 : ℕ, 0 < a0 → 0 < a1 → 0 < a2 →
        f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (n3a : ℝ) / D_x] +
        f ![(a0 : ℝ) / D_x, (a1 : ℝ) / D_x, (a2 : ℝ) / D_x, (n3b : ℝ) / D_x] ≤
        ((ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * n3a) + ceilDiv (S_v * D_x5) (a0 * a1 * a2 * a2 * n3b) : ℕ) : ℝ) / S_v := by
      intro a0 a1 a2 ha0 ha1 ha2; rw [Nat.cast_add, add_div]; linarith only [hv_le a0 a1 a2 n3a ha0 ha1 ha2 h3p, hv_le a0 a1 a2 n3b ha0 ha1 ha2 h3bp]
    dsimp only [sv]
    refine sumVerts3R_le knd ht01 ht12 hts (fun a0 a1 a2 ha0 ha1 ha2 => ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    exact hp3 a0 a1 a2 (by rcases ha0 with rfl | rfl <;> assumption) (by rcases ha1 with rfl | rfl <;> assumption)
      (by rcases ha2 with rfl | rfl <;> assumption)
  set wm := ceilDiv (S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv) (facDen knd * (2 * nVerts3 knd) * D_x4 * S_v)
  have hwm_le : ∫ x in C, f x ≤ (wm : ℝ) / S_4 := by
    have hvol_nn : 0 ≤ ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
        ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) * ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x) /
        ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ))) := by
      have : (0 : ℝ) ≤ (n0b : ℝ) / D_x - (n0a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h0le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n1b : ℝ) / D_x - (n1a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h1le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n2b : ℝ) / D_x - (n2a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h2le) (le_of_lt hDx))
      have : (0 : ℝ) ≤ (n3b : ℝ) / D_x - (n3a : ℝ) / D_x := sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast h3le) (le_of_lt hDx))
      have : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
      have : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
      positivity
    have hstep := le_trans hhh (mul_le_mul_of_nonneg_left hsum_le hvol_nn)
    refine le_trans hstep ?_
    have hden_nat : 0 < facDen knd * (2 * nVerts3 knd) * D_x4 * S_v :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by cases knd <;> simp [facDen]) (Nat.mul_pos (by decide) (by cases knd <;> simp [nVerts3]))) (hDx4_nat_pos hp)) (hSv_nat_pos hp)
    have hcd : ((S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv : ℕ) : ℝ) ≤
        ((facDen knd * (2 * nVerts3 knd) * D_x4 * S_v : ℕ) : ℝ) * (wm : ℝ) := by exact_mod_cast le_mul_ceilDiv hden_nat
    have hfd_pos : (0 : ℝ) < facDen knd := by cases knd <;> simp [facDen]
    have hnv_pos : (0 : ℝ) < nVerts3 knd := by cases knd <;> simp [nVerts3]
    rw [le_div_iff₀ (hS4_pos hp)]
    have hLHS : ((n0b : ℝ) / D_x - (n0a : ℝ) / D_x) * ((n1b : ℝ) / D_x - (n1a : ℝ) / D_x) *
        ((n2b : ℝ) / D_x - (n2a : ℝ) / D_x) * ((n3b : ℝ) / D_x - (n3a : ℝ) / D_x) /
        ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ))) * ((sv : ℝ) / S_v) * S_4 =
        ((S_4 * (n0b - n0a) * (n1b - n1a) * (n2b - n2a) * (n3b - n3a) * sv : ℕ) : ℝ) /
        ((facDen knd * (2 * nVerts3 knd) * D_x4 * S_v : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, (D_x4_cast hp)]
      rw [Nat.cast_sub h0le, Nat.cast_sub h1le, Nat.cast_sub h2le, Nat.cast_sub h3le]
      field_simp [ne_of_gt hDx, ne_of_gt hfd_pos, ne_of_gt hnv_pos, ne_of_gt (hSv_pos hp)]; ring
    rw [hLHS, div_le_iff₀ (by exact_mod_cast hden_nat)]; linarith
  have hcomb := le_trans hle1 (mul_le_mul_of_nonneg_left hwm_le (by positivity))
  refine le_trans hcomb ?_
  unfold Buchstab4DT.eval4TransLeaf; dsimp only
  have hcd : ((om_ub * wm : ℕ) : ℝ) ≤ (S_v : ℝ) * (ceilDiv (om_ub * wm) S_v : ℝ) := by
    exact_mod_cast le_mul_ceilDiv (a := om_ub * wm) ((hSv_nat_pos hp))
  rw [show ((om_ub : ℝ) / S_v) * ((wm : ℝ) / S_4) = ((om_ub * wm : ℕ) : ℝ) / ((S_v : ℝ) * S_4) by push_cast; ring]
  rw [div_le_div_iff₀ (mul_pos (hSv_pos hp) (hS4_pos hp)) (hS4_pos hp)]; nlinarith

/-! ### Part 6B: Tree-Additivity for 4D Integrals (`evalTree4`) -/

lemma evalTree4_sound {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (φ : ℝ)
    (hlf : ∀ knd n0a n0b n1a n1b n2a n2b n3a n3b,
      cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                          ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (lfFn knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / S_4)
    (t : BoxTree4) :
    ∀ (knd : CellKind) (n0a n0b n1a n1b n2a n2b n3a n3b : ℕ),
      tree4Valid knd t = true →
      cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                          ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (evalTree4 lfFn knd t n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / S_4 := by
  have hDx := (hDx_pos hp)
  have hnn_cell : ∀ knd n0a n0b n1a n1b n2a n2b n3a n3b,
      cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∀ x ∈ cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                         ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x),
        0 ≤ ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) := by
    intro knd n0a n0b n1a n1b n2a n2b n3a n3b hv x hx
    rcases hv with ⟨⟨hA0, _, _, hA1, _, _, hA2, _, _, ht01, ht12, hts⟩, hBa3, _, _⟩
    have h0' : 0 < x 0 := lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA0)) hDx) (by cases knd <;> exact hx.1.1)
    have h1' : 0 < x 1 := by
      cases knd with
      | box => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA1)) hDx) hx.2.1.1
      | tri01 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA0)) hDx) hx.2.1.1
      | tri12 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA1)) hDx) hx.2.1.1
      | simp => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA0)) hDx) hx.2.1.1
    have h2' : 0 < x 2 := by
      cases knd with
      | box => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA2)) hDx) hx.2.2.1.1
      | tri01 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA2)) hDx) hx.2.2.1.1
      | tri12 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA1)) hDx) hx.2.2.1.1
      | simp => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA0)) hDx) hx.2.2.1.1
    have h3' : 0 < x 3 := by
      cases knd with
      | box => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (B_n_pos hp) hBa3)) hDx) hx.2.2.2.1
      | tri01 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (B_n_pos hp) hBa3)) hDx) hx.2.2.2.1.1
      | tri12 => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (B_n_pos hp) hBa3)) hDx) hx.2.2.2.1.1
      | simp => exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (B_n_pos hp) hBa3)) hDx) hx.2.2.2.1.1
    exact div_nonneg (buchstab_nonneg hω _) (by rw [Fin.prod_univ_four]; positivity)
  have hint_cell : ∀ knd n0a n0b n1a n1b n2a n2b n3a n3b,
      cell4Valid knd n0a n0b n1a n1b n2a n2b n3a n3b →
      IntegrableOn (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2))
        (cell4Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x)
                      ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x) ((n3a : ℝ) / D_x) ((n3b : ℝ) / D_x)) volume := by
    intro knd n0a n0b n1a n1b n2a n2b n3a n3b hv
    rcases hv with ⟨⟨hA0, _, _, hA1, _, _, hA2, _, _, _, _, _⟩, hBa3, _, _⟩
    exact integrand4_integrableOn hp hω φ
      (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA0)) hDx)
      (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA1)) hDx)
      (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (A_n_pos hp) hA2)) hDx)
      (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (B_n_pos hp) hBa3)) hDx)
  induction t with
  | lf => intro knd a0 b0 a1 b1 a2 b2 a3 b3 _ hv; exact hlf knd a0 b0 a1 b1 a2 b2 a3 b3 hv
  | s0 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    set m := (a0 + b0) / 2
    rcases hv with ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩, hBa3, h3le, h3C⟩
    have hml : a0 ≤ m := by omega
    have hmr : m ≤ b0 := by omega
    cases knd with
    | box =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      have hvl : cell4Valid .box a0 m a1 b1 a2 b2 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, hA1, h1le, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hvr : cell4Valid .box m b0 a1 b1 a2 b2 a3 b3 := ⟨⟨le_trans hA0 hml, hmr, h0B, hA1, h1le, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hsub : cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
          cell4Set .box ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ∪
          cell4Set .box ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
        intro x hx; rcases le_total (x 0) ((m : ℝ) / D_x) with h | h
        · left; exact ⟨⟨hx.1.1, h⟩, hx.2⟩
        · right; exact ⟨⟨h, hx.1.2⟩, hx.2⟩
      have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
        (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ihl .box a0 m a1 b1 a2 b2 a3 b3 htv.1 hvl; have h2 := ihr .box m b0 a1 b1 a2 b2 a3 b3 htv.2 hvr; linarith only [hle, h1, h2]
    | tri12 =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      rcases ht12 rfl with ⟨rfl, rfl⟩
      have hvl : cell4Valid .tri12 a0 m a1 b1 a1 b1 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, hA1, h1le, h1B, hA1, h1le, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩, hBa3, h3le, h3C⟩
      have hvr : cell4Valid .tri12 m b0 a1 b1 a1 b1 a3 b3 := ⟨⟨le_trans hA0 hml, hmr, h0B, hA1, h1le, h1B, hA1, h1le, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩, hBa3, h3le, h3C⟩
      have hsub : cell4Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
          cell4Set .tri12 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ∪
          cell4Set .tri12 ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
        intro x hx; rcases le_total (x 0) ((m : ℝ) / D_x) with h | h
        · left; exact ⟨⟨hx.1.1, h⟩, hx.2⟩
        · right; exact ⟨⟨h, hx.1.2⟩, hx.2⟩
      have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
        (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ihl .tri12 a0 m a1 b1 a1 b1 a3 b3 htv.1 hvl; have h2 := ihr .tri12 m b0 a1 b1 a1 b1 a3 b3 htv.2 hvr; linarith only [hle, h1, h2]
    | tri01 => simp [tree4Valid] at htv
    | simp => simp [tree4Valid] at htv
  | s1 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    set m := (a1 + b1) / 2
    rcases hv with ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, _, _, _⟩, hBa3, h3le, h3C⟩
    have hml : a1 ≤ m := by omega
    have hmr : m ≤ b1 := by omega
    cases knd with
    | box =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      have hvl : cell4Valid .box a0 b0 a1 m a2 b2 a3 b3 := ⟨⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hvr : cell4Valid .box a0 b0 m b1 a2 b2 a3 b3 := ⟨⟨hA0, h0le, h0B, le_trans hA1 hml, hmr, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hsub : cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
          cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ∪
          cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
        intro x hx; rcases le_total (x 1) ((m : ℝ) / D_x) with h | h
        · left; exact ⟨hx.1, ⟨hx.2.1.1, h⟩, hx.2.2⟩
        · right; exact ⟨hx.1, ⟨h, hx.2.1.2⟩, hx.2.2⟩
      have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
        (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ihl .box a0 b0 a1 m a2 b2 a3 b3 htv.1 hvl; have h2 := ihr .box a0 b0 m b1 a2 b2 a3 b3 htv.2 hvr; linarith only [hle, h1, h2]
    | _ => simp [tree4Valid] at htv
  | s2 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    set m := (a2 + b2) / 2
    rcases hv with ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, _, _⟩, hBa3, h3le, h3C⟩
    have hml : a2 ≤ m := by omega
    have hmr : m ≤ b2 := by omega
    cases knd with
    | box =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      have hvl : cell4Valid .box a0 b0 a1 b1 a2 m a3 b3 := ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, hml, le_trans hmr h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hvr : cell4Valid .box a0 b0 a1 b1 m b2 a3 b3 := ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, le_trans hA2 hml, hmr, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hsub : cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
          cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((m : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ∪
          cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((m : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
        intro x hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h | h
        · left; exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1.1, h⟩, hx.2.2.2⟩
        · right; exact ⟨hx.1, hx.2.1, ⟨h, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
        (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ihl .box a0 b0 a1 b1 a2 m a3 b3 htv.1 hvl; have h2 := ihr .box a0 b0 a1 b1 m b2 a3 b3 htv.2 hvr; linarith only [hle, h1, h2]
    | tri01 =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      rcases ht01 rfl with ⟨rfl, rfl⟩
      have hvl : cell4Valid .tri01 a0 b0 a0 b0 a2 m a3 b3 := ⟨⟨hA0, h0le, h0B, hA0, h0le, h0B, hA2, hml, le_trans hmr h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hvr : cell4Valid .tri01 a0 b0 a0 b0 m b2 a3 b3 := ⟨⟨hA0, h0le, h0B, hA0, h0le, h0B, le_trans hA2 hml, hmr, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hsub : cell4Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
          cell4Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((m : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ∪
          cell4Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
        intro x hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h | h
        · left; exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1.1, h⟩, hx.2.2.2⟩
        · right; exact ⟨hx.1, hx.2.1, ⟨h, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
        (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ihl .tri01 a0 b0 a0 b0 a2 m a3 b3 htv.1 hvl; have h2 := ihr .tri01 a0 b0 a0 b0 m b2 a3 b3 htv.2 hvr; linarith only [hle, h1, h2]
    | _ => simp [tree4Valid] at htv
  | s3 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    set m := (a3 + b3) / 2
    simp only [tree4Valid, Bool.and_eq_true] at htv
    rcases hv with ⟨hv3, hBa3, h3le, h3C⟩
    have hml : a3 ≤ m := by omega
    have hmr : m ≤ b3 := by omega
    have hvl : cell4Valid knd a0 b0 a1 b1 a2 b2 a3 m := ⟨hv3, hBa3, hml, le_trans hmr h3C⟩
    have hvr : cell4Valid knd a0 b0 a1 b1 a2 b2 m b3 := ⟨hv3, le_trans hBa3 hml, hmr, h3C⟩
    have hsub : cell4Set knd ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆
        cell4Set knd ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((m : ℝ) / D_x) ∪
        cell4Set knd ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((m : ℝ) / D_x) ((b3 : ℝ) / D_x) := by
      intro x hx; rcases le_total (x 3) ((m : ℝ) / D_x) with h | h
      · left; cases knd with
        | box => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨hx.2.2.2.1, h⟩⟩
        | tri01 => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨hx.2.2.2.1.1, h⟩, hx.2.2.2.2⟩
        | tri12 => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨hx.2.2.2.1.1, h⟩, hx.2.2.2.2⟩
        | simp => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨hx.2.2.2.1.1, h⟩, hx.2.2.2.2⟩
      · right; cases knd with
        | box => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨h, hx.2.2.2.2⟩⟩
        | tri01 => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨h, hx.2.2.2.1.2⟩, hx.2.2.2.2⟩
        | tri12 => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨h, hx.2.2.2.1.2⟩, hx.2.2.2.2⟩
        | simp => exact ⟨hx.1, hx.2.1, hx.2.2.1, ⟨h, hx.2.2.2.1.2⟩, hx.2.2.2.2⟩
    have hle := setIntegral_le_sum2_4 hsub (cell4Set_isClosed knd _ _ _ _ _ _ _ _).measurableSet
      (cell4Set_isClosed knd _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvl) (hnn_cell _ _ _ _ _ _ _ _ _ hvr)
      (hint_cell _ _ _ _ _ _ _ _ _ hvl) (hint_cell _ _ _ _ _ _ _ _ _ hvr)
    simp only [evalTree4, Nat.cast_add, add_div]
    have h1 := ihl knd a0 b0 a1 b1 a2 b2 a3 m htv.1 hvl; have h2 := ihr knd a0 b0 a1 b1 a2 b2 m b3 htv.2 hvr; linarith only [hle, h1, h2]
  | sd01 c0 mm c1 ih0 ihm ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    cases knd with
    | tri01 =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨⟨hA0, h0le, h0B, _, _, _, hA2, h2le, h2B, ht01, _, _⟩, hBa3, h3le, h3C⟩
      rcases ht01 rfl with ⟨rfl, rfl⟩
      set m := (a0 + b0) / 2
      have hml : a0 ≤ m := by omega
      have hmr : m ≤ b0 := by omega
      have hv0 : cell4Valid .tri01 a0 m a0 m a2 b2 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, hA2, h2le, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hvm : cell4Valid .box a0 m m b0 a2 b2 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, hA2, h2le, h2B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hv1 : cell4Valid .tri01 m b0 m b0 a2 b2 a3 b3 := ⟨⟨le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, hA2, h2le, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩, hBa3, h3le, h3C⟩
      set S0 := cell4Set .tri01 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set Sm := cell4Set .box ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set S1 := cell4Set .tri01 ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      have hsub : cell4Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆ (S0 ∪ Sm) ∪ S1 := by
        intro x hx; rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
        · left; left; exact ⟨⟨hx.1.1, le_trans hx.2.2.2.2 h1m⟩, ⟨hx.2.1.1, h1m⟩, hx.2.2⟩
        · rcases le_total (x 0) ((m : ℝ) / D_x) with h0m | h0m
          · left; right; exact ⟨⟨hx.1.1, h0m⟩, ⟨h1m, hx.2.1.2⟩, hx.2.2.1, hx.2.2.2.1⟩
          · right; exact ⟨⟨h0m, hx.1.2⟩, ⟨h1m, hx.2.1.2⟩, hx.2.2⟩
      have hle1 := setIntegral_le_sum2_4 hsub
        ((cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet.union (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet)
        (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet
        (by rintro x (hx | hx); exact hnn_cell _ _ _ _ _ _ _ _ _ hv0 x hx; exact hnn_cell _ _ _ _ _ _ _ _ _ hvm x hx)
        (hnn_cell _ _ _ _ _ _ _ _ _ hv1)
        ((hint_cell _ _ _ _ _ _ _ _ _ hv0).union (hint_cell _ _ _ _ _ _ _ _ _ hvm))
        (hint_cell _ _ _ _ _ _ _ _ _ hv1)
      have hle2 := setIntegral_union_le_of_nonneg (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvm)
        (hint_cell _ _ _ _ _ _ _ _ _ hv0) (hint_cell _ _ _ _ _ _ _ _ _ hvm)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ih0 .tri01 a0 m a0 m a2 b2 a3 b3 htv.1.1 hv0; have h2 := ihm .box a0 m m b0 a2 b2 a3 b3 htv.1.2 hvm; have h3 := ih1 .tri01 m b0 m b0 a2 b2 a3 b3 htv.2 hv1; linarith only [hle1, hle2, h1, h2, h3]
    | _ => simp [tree4Valid] at htv
  | sd12 c0 mm c1 ih0 ihm ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    cases knd with
    | tri12 =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨⟨hA0, h0le, h0B, hA1, h1le, h1B, _, _, _, _, ht12, _⟩, hBa3, h3le, h3C⟩
      rcases ht12 rfl with ⟨rfl, rfl⟩
      set m := (a1 + b1) / 2
      have hml : a1 ≤ m := by omega
      have hmr : m ≤ b1 := by omega
      have hv0 : cell4Valid .tri12 a0 b0 a1 m a1 m a3 b3 := ⟨⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, hA1, hml, le_trans hmr h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩, hBa3, h3le, h3C⟩
      have hvm : cell4Valid .box a0 b0 a1 m m b1 a3 b3 := ⟨⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, le_trans hA1 hml, hmr, h1B, by simp, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hv1 : cell4Valid .tri12 a0 b0 m b1 m b1 a3 b3 := ⟨⟨hA0, h0le, h0B, le_trans hA1 hml, hmr, h1B, le_trans hA1 hml, hmr, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩, hBa3, h3le, h3C⟩
      set S0 := cell4Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set Sm := cell4Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set S1 := cell4Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      have hsub : cell4Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆ (S0 ∪ Sm) ∪ S1 := by
        intro x hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h2m | h2m
        · left; left; exact ⟨hx.1, ⟨hx.2.1.1, le_trans hx.2.2.2.2 h2m⟩, ⟨hx.2.2.1.1, h2m⟩, hx.2.2.2⟩
        · rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
          · left; right; exact ⟨hx.1, ⟨hx.2.1.1, h1m⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2.1⟩
          · right; exact ⟨hx.1, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hle1 := setIntegral_le_sum2_4 hsub
        ((cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet.union (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet)
        (cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet
        (by rintro x (hx | hx); exact hnn_cell _ _ _ _ _ _ _ _ _ hv0 x hx; exact hnn_cell _ _ _ _ _ _ _ _ _ hvm x hx)
        (hnn_cell _ _ _ _ _ _ _ _ _ hv1)
        ((hint_cell _ _ _ _ _ _ _ _ _ hv0).union (hint_cell _ _ _ _ _ _ _ _ _ hvm))
        (hint_cell _ _ _ _ _ _ _ _ _ hv1)
      have hle2 := setIntegral_union_le_of_nonneg (cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .box _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hvm)
        (hint_cell _ _ _ _ _ _ _ _ _ hv0) (hint_cell _ _ _ _ _ _ _ _ _ hvm)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ih0 .tri12 a0 b0 a1 m a1 m a3 b3 htv.1.1 hv0; have h2 := ihm .box a0 b0 a1 m m b1 a3 b3 htv.1.2 hvm; have h3 := ih1 .tri12 a0 b0 m b1 m b1 a3 b3 htv.2 hv1; linarith only [hle1, hle2, h1, h2, h3]
    | _ => simp [tree4Valid] at htv
  | sd012 c0 m01 m12 c1 ih0 ih01 ih12 ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 a3 b3 htv hv
    cases knd with
    | simp =>
      simp only [tree4Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨⟨hA0, h0le, h0B, _, _, _, _, _, _, _, _, hts⟩, hBa3, h3le, h3C⟩
      rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩
      set m := (a0 + b0) / 2
      have hml : a0 ≤ m := by omega
      have hmr : m ≤ b0 := by omega
      have hv0 : cell4Valid .simp a0 m a0 m a0 m a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, by simp, by simp, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩, hBa3, h3le, h3C⟩
      have hv01 : cell4Valid .tri01 a0 m a0 m m b0 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩, hBa3, h3le, h3C⟩
      have hv12 : cell4Valid .tri12 a0 m m b0 m b0 a3 b3 := ⟨⟨hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩, hBa3, h3le, h3C⟩
      have hv1 : cell4Valid .simp m b0 m b0 m b0 a3 b3 := ⟨⟨le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, by simp, by simp, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩, hBa3, h3le, h3C⟩
      set S0 := cell4Set .simp ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set S01 := cell4Set .tri01 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set S12 := cell4Set .tri12 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      set S1 := cell4Set .simp ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x)
      have hsub : cell4Set .simp ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a3 : ℝ) / D_x) ((b3 : ℝ) / D_x) ⊆ (S0 ∪ S01) ∪ (S12 ∪ S1) := by
        intro x hx
        rcases le_total (x 2) ((m : ℝ) / D_x) with h2m | h2m
        · left; left; exact ⟨⟨hx.1.1, le_trans hx.2.2.2.2.1 (le_trans hx.2.2.2.2.2 h2m)⟩, ⟨hx.2.1.1, le_trans hx.2.2.2.2.2 h2m⟩, ⟨hx.2.2.1.1, h2m⟩, hx.2.2.2⟩
        · rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
          · left; right; exact ⟨⟨hx.1.1, le_trans hx.2.2.2.2.1 h1m⟩, ⟨hx.2.1.1, h1m⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2.1, hx.2.2.2.2.1⟩
          · rcases le_total (x 0) ((m : ℝ) / D_x) with h0m | h0m
            · right; left; exact ⟨⟨hx.1.1, h0m⟩, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2.1, hx.2.2.2.2.2⟩
            · right; right; exact ⟨⟨h0m, hx.1.2⟩, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hle1 := setIntegral_le_sum2_4 hsub
        ((cell4Set_isClosed .simp _ _ _ _ _ _ _ _).measurableSet.union (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet)
        ((cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet.union (cell4Set_isClosed .simp _ _ _ _ _ _ _ _).measurableSet)
        (by rintro x (hx | hx); exact hnn_cell _ _ _ _ _ _ _ _ _ hv0 x hx; exact hnn_cell _ _ _ _ _ _ _ _ _ hv01 x hx)
        (by rintro x (hx | hx); exact hnn_cell _ _ _ _ _ _ _ _ _ hv12 x hx; exact hnn_cell _ _ _ _ _ _ _ _ _ hv1 x hx)
        ((hint_cell _ _ _ _ _ _ _ _ _ hv0).union (hint_cell _ _ _ _ _ _ _ _ _ hv01))
        ((hint_cell _ _ _ _ _ _ _ _ _ hv12).union (hint_cell _ _ _ _ _ _ _ _ _ hv1))
      have hle2 := setIntegral_union_le_of_nonneg (cell4Set_isClosed .simp _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .tri01 _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hv01)
        (hint_cell _ _ _ _ _ _ _ _ _ hv0) (hint_cell _ _ _ _ _ _ _ _ _ hv01)
      have hle3 := setIntegral_union_le_of_nonneg (cell4Set_isClosed .tri12 _ _ _ _ _ _ _ _).measurableSet
        (cell4Set_isClosed .simp _ _ _ _ _ _ _ _).measurableSet (hnn_cell _ _ _ _ _ _ _ _ _ hv1)
        (hint_cell _ _ _ _ _ _ _ _ _ hv12) (hint_cell _ _ _ _ _ _ _ _ _ hv1)
      simp only [evalTree4, Nat.cast_add, add_div]
      have h1 := ih0 .simp a0 m a0 m a0 m a3 b3 htv.1.1.1 hv0; have h2 := ih01 .tri01 a0 m a0 m m b0 a3 b3 htv.1.1.2 hv01; have h3 := ih12 .tri12 a0 m m b0 m b0 a3 b3 htv.1.2 hv12; have h4 := ih1 .simp m b0 m b0 m b0 a3 b3 htv.2 hv1; linarith only [hle1, hle2, hle3, h1, h2, h3, h4]
    | _ => simp [tree4Valid] at htv

/-! ### Part 6C: Exact Difference Identity & Soundness of `evalTree3` (`M_+` and `M_-`) -/

lemma I_fn_eq_G {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {φ : ℝ} (hφ_top : φ ≤ 5 * A_R + B_R) :
    I_fn ω φ = ∫ y in cell3Set .simp A_R B_R A_R B_R A_R B_R,
      (1 / (y 0 * y 1 * y 2)) * G_fn φ y := by
  unfold Buchstab4DT.I_fn
  let g : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
    ω ((φ - (p.2 0 + p.2 1 + p.2 2 + p.1)) / p.2 2) / ((p.2 0 * p.2 1 * p.2 2 * p.1) * p.2 2)
  have hf_eq : (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) = g ∘ equivFin4_3 := by
    ext x; dsimp only [g, Function.comp_apply]; rw [equivFin4_3_apply, Fin.sum_univ_four, Fin.prod_univ_four]; simp
  have hint4 := integrand4_integrableOn hp hω φ (knd := .simp) (hA_pos hp) (hA_pos hp) (hA_pos hp) (lt_trans (hA_pos hp) (hAB_lt hp)) (b0 := B_R) (b1 := B_R) (b2 := B_R) (b3 := C_R)
  rw [cell4Set_eq_preimage, hf_eq] at hint4 ⊢
  change ∫ x in equivFin4_3 ⁻¹' (Icc B_R C_R ×ˢ cell3Set .simp A_R B_R A_R B_R A_R B_R), g (equivFin4_3 x) = _
  rw [volume_preserving_equivFin4_3.setIntegral_preimage_emb equivFin4_3.measurableEmbedding]
  have hint_prod : IntegrableOn g (Icc B_R C_R ×ˢ cell3Set .simp A_R B_R A_R B_R A_R B_R) (volume.prod volume) :=
    (volume_preserving_equivFin4_3.integrableOn_comp_preimage equivFin4_3.measurableEmbedding).mp hint4
  rw [setIntegral_prod_symm' _ hint_prod]
  apply setIntegral_congr_fun (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet
  intro y hy; dsimp only
  have hy0 : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hy.1.1
  have hy1 : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hy.2.1.1
  have hy2 : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hy.2.2.1.1
  set m := max B_R (min C_R (φ - y 0 - y 1 - 2 * y 2))
  have hBm : B_R ≤ m := le_max_left _ _
  have hmC : m ≤ C_R := max_le (le_of_lt (hBC_lt hp)) (min_le_left _ _)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt (hBC_lt hp))]
  have hsplit_int : IntervalIntegrable (fun x3 => g (x3, y)) volume B_R C_R := by
    have hPm : MeasurableSet {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} := measurableSet_Iic
    have heq_ind : ∀ x3 ∈ Icc B_R C_R, g (x3, y) =
        ({x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2}).indicator
          (fun x3 => (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3)))) x3 := by
      intro x3 hx3; dsimp only [g]
      by_cases hle : x3 ≤ φ - y 0 - y 1 - 2 * y 2
      · rw [Set.indicator_of_mem (show x3 ∈ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from hle)]
        have hu1 : 1 ≤ (φ - (y 0 + y 1 + y 2 + x3)) / y 2 := (one_le_div hy2).mpr (by linarith)
        have hu2 : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 ≤ 2 := (div_le_iff₀ hy2).mpr (by linarith [hy.1.1, hy.2.1.1, hy.2.2.1.1, hx3.1])
        rw [hω.2.1 _ hu1 hu2]
        have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
        have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by linarith
        have hrem' : φ - (y 0 + y 1 + y 2 + x3) = φ - (y 0 + y 1 + y 2) - x3 := by ring
        rw [hrem']; field_simp [ne_of_gt hy0, ne_of_gt hy1, ne_of_gt hy2, ne_of_gt hx3p, ne_of_gt hrem]
      · rw [Set.indicator_of_notMem (show x3 ∉ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from hle)]
        have hlt : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 < 1 := (div_lt_one hy2).mpr (by linarith)
        rw [hω.2.2.2 _ hlt, zero_div]
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt (hBC_lt hp))).mpr ?_
    rw [integrableOn_congr_fun heq_ind measurableSet_Icc, integrableOn_indicator_iff hPm, inter_comm]
    have hcont_sub : ContinuousOn (fun x3 => (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3))))
        (Icc B_R C_R ∩ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2}) := by
      refine continuousOn_const.mul (continuousOn_const.div (by fun_prop) ?_)
      intro x3 ⟨hx3, hle⟩
      have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
      have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by change x3 ≤ _ at hle; linarith
      positivity
    exact hcont_sub.integrableOn_compact (isCompact_Icc.inter_right (show IsClosed {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from isClosed_Iic))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hsplit_int.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le (le_of_lt (hBC_lt hp))]; exact ⟨hBm, hmC⟩)))
    (hsplit_int.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le (le_of_lt (hBC_lt hp))]; exact ⟨hBm, hmC⟩)))]
  have hright_zero : ∫ x3 in m..C_R, g (x3, y) = 0 := by
    rw [intervalIntegral.integral_of_le hmC]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x3 hx3
    have hgt : φ - y 0 - y 1 - 2 * y 2 < x3 := by
      by_cases hmc : m = C_R
      · exfalso; linarith [hx3.1, hx3.2]
      · have hle_m : min C_R (φ - y 0 - y 1 - 2 * y 2) ≤ m := le_max_right _ _
        have hlt_c : φ - y 0 - y 1 - 2 * y 2 < C_R := by
          by_contra hge; push Not at hge
          have : m = C_R := by dsimp only [m]; rw [min_eq_left hge, max_eq_right (le_of_lt (hBC_lt hp))]
          exact hmc this
        have : φ - y 0 - y 1 - 2 * y 2 ≤ m := by dsimp only [m]; rw [min_eq_right (le_of_lt hlt_c)]; exact le_max_right _ _
        linarith [hx3.1]
    have hlt : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 < 1 := (div_lt_one hy2).mpr (by linarith)
    dsimp only [g]; rw [hω.2.2.2 _ hlt, zero_div]
  rw [hright_zero, add_zero]
  by_cases hmB : m = B_R
  · rw [hmB, intervalIntegral.integral_same]
    dsimp only [Buchstab4DT.G_fn]; change (0 : ℝ) = (1 / (y 0 * y 1 * y 2)) * ∫ x3 in B_R..m, _
    rw [hmB, intervalIntegral.integral_same, mul_zero]
  · have hleft_eq : ∀ x3 ∈ uIcc B_R m, g (x3, y) =
        (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3))) := by
      intro x3 hx3; rw [uIcc_of_le hBm] at hx3
      dsimp only [g]
      have hle_cut : x3 ≤ φ - y 0 - y 1 - 2 * y 2 := by
        have : m = min C_R (φ - y 0 - y 1 - 2 * y 2) := by
          dsimp only [m]; exact max_eq_right (by by_contra hlt; push Not at hlt; exact hmB (max_eq_left (le_of_lt hlt)))
        have : m ≤ φ - y 0 - y 1 - 2 * y 2 := by rw [this]; exact min_le_right _ _
        linarith [hx3.2]
      have hu1 : 1 ≤ (φ - (y 0 + y 1 + y 2 + x3)) / y 2 := (one_le_div hy2).mpr (by linarith)
      have hu2 : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 ≤ 2 := (div_le_iff₀ hy2).mpr (by linarith [hy.1.1, hy.2.1.1, hy.2.2.1.1, hx3.1])
      rw [hω.2.1 _ hu1 hu2]
      have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
      have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by linarith
      have hrem' : φ - (y 0 + y 1 + y 2 + x3) = φ - (y 0 + y 1 + y 2) - x3 := by ring
      rw [hrem']; field_simp [ne_of_gt hy0, ne_of_gt hy1, ne_of_gt hy2, ne_of_gt hx3p, ne_of_gt hrem]
    rw [intervalIntegral.integral_congr hleft_eq, intervalIntegral.integral_const_mul]; rfl

/-! ### Part 6D: Exact Pointwise Difference Decomposition of `G_fn` -/

lemma G_fn_sub_eq {φ1 φ2 : ℝ} (h12 : φ1 < φ2) {y : Fin 3 → ℝ}
    (hy2 : 0 < y 2) :
    let m1 := max B_R (min C_R (φ1 - y 0 - y 1 - 2 * y 2))
    let m2 := max B_R (min C_R (φ2 - y 0 - y 1 - 2 * y 2))
    G_fn φ2 y - G_fn φ1 y =
      (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) -
      (φ2 - φ1) * (∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3))) := by
  intro m1 m2
  have hBpos : 0 < B_R := lt_trans (hA_pos hp) (hAB_lt hp)
  have hBm1 : B_R ≤ m1 := le_max_left _ _
  have hm12 : m1 ≤ m2 := max_le_max_left B_R (min_le_min_left C_R (by linarith))
  have hBm2 : B_R ≤ m2 := le_trans hBm1 hm12
  by_cases hm1B : m1 = B_R
  · unfold Buchstab4DT.G_fn; dsimp only [m1, m2] at hm1B ⊢; rw [hm1B]; simp
  · have hm1_le_cut : m1 ≤ φ1 - y 0 - y 1 - 2 * y 2 := by
      have : m1 = min C_R (φ1 - y 0 - y 1 - 2 * y 2) :=
        max_eq_right (by by_contra hlt; push Not at hlt; exact hm1B (max_eq_left (le_of_lt hlt)))
      rw [this]; exact min_le_right _ _
    have hm2_le_cut : m2 ≤ φ2 - y 0 - y 1 - 2 * y 2 := by
      have hm2B : m2 ≠ B_R := fun h => hm1B (le_antisymm (h ▸ hm12) hBm1)
      have : m2 = min C_R (φ2 - y 0 - y 1 - 2 * y 2) :=
        max_eq_right (by by_contra hlt; push Not at hlt; exact hm2B (max_eq_left (le_of_lt hlt)))
      rw [this]; exact min_le_right _ _
    have hc2 : ContinuousOn (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) (Icc B_R m2) := by
      refine continuousOn_const.div (by fun_prop) ?_
      intro x3 hx3; have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
      have : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm2_le_cut]
      positivity
    have hc1 : ContinuousOn (fun x3 => 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3))) (Icc B_R m1) := by
      refine continuousOn_const.div (by fun_prop) ?_
      intro x3 hx3; have : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
      have : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm1_le_cut]
      positivity
    have hi2_all : IntervalIntegrable (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) volume B_R m2 :=
      hc2.intervalIntegrable_of_Icc hBm2
    have hi2_1 : IntervalIntegrable (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) volume B_R m1 :=
      hi2_all.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hBm2]; exact ⟨hBm1, hm12⟩))
    have hi2_2 : IntervalIntegrable (fun x3 => 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) volume m1 m2 :=
      hi2_all.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hBm2]; exact ⟨hBm1, hm12⟩))
    have hi1 : IntervalIntegrable (fun x3 => 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3))) volume B_R m1 :=
      hc1.intervalIntegrable_of_Icc hBm1
    unfold Buchstab4DT.G_fn
    rw [← intervalIntegral.integral_add_adjacent_intervals hi2_1 hi2_2]
    have hdiff_eq : (∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3))) -
        (∫ x3 in B_R..m1, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) =
        (φ2 - φ1) * ∫ x3 in B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)) := by
      rw [← intervalIntegral.integral_sub hi1 hi2_1, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x3 hx3; rw [uIcc_of_le hBm1] at hx3
      have hx3p : 0 < x3 := lt_of_lt_of_le hBpos hx3.1
      have hr1 : 0 < φ1 - (y 0 + y 1 + y 2) - x3 := by linarith [hx3.2, hm1_le_cut]
      have hr2 : 0 < φ2 - (y 0 + y 1 + y 2) - x3 := by linarith
      field_simp [ne_of_gt hx3p, ne_of_gt hr1, ne_of_gt hr2]; ring
    linarith

-- Integrability of (1 / (y 0 * y 1 * y 2)) * G_fn φ y on any valid cell3Set
lemma G_fn_integrableOn {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {φ : ℝ} (hφ_top : φ ≤ 5 * A_R + B_R)
    {knd : CellKind} {n0a n0b n1a n1b n2a n2b : ℕ}
    (hv : cell3Valid knd n0a n0b n1a n1b n2a n2b) :
    IntegrableOn (fun y : Fin 3 → ℝ => (1 / (y 0 * y 1 * y 2)) * G_fn φ y)
      (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) volume := by
  -- Follows directly from Fubini on the 4D integrable Buchstab integrand!
  have hDx := (hDx_pos hp)
  rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
  have h0p : 0 < n0a := lt_of_lt_of_le (A_n_pos hp) hA0
  have h1p : 0 < n1a := lt_of_lt_of_le (A_n_pos hp) hA1
  have h2p : 0 < n2a := lt_of_lt_of_le (A_n_pos hp) hA2
  let g : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
    ω ((φ - (p.2 0 + p.2 1 + p.2 2 + p.1)) / p.2 2) / ((p.2 0 * p.2 1 * p.2 2 * p.1) * p.2 2)
  have hf_eq : (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) = g ∘ equivFin4_3 := by
    ext x; dsimp only [g, Function.comp_apply]; rw [equivFin4_3_apply, Fin.sum_univ_four, Fin.prod_univ_four]; simp
  have hint4 := integrand4_integrableOn hp hω φ (knd := knd)
    (div_pos (Nat.cast_pos.mpr h0p) hDx) (div_pos (Nat.cast_pos.mpr h1p) hDx)
    (div_pos (Nat.cast_pos.mpr h2p) hDx) (lt_trans (hA_pos hp) (hAB_lt hp))
    (b0 := (n0b : ℝ) / D_x) (b1 := (n1b : ℝ) / D_x) (b2 := (n2b : ℝ) / D_x) (b3 := C_R)
  rw [cell4Set_eq_preimage, hf_eq] at hint4
  have hint_prod : IntegrableOn g (Icc B_R C_R ×ˢ
      cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x))
      (volume.prod volume) :=
    (volume_preserving_equivFin4_3.integrableOn_comp_preimage equivFin4_3.measurableEmbedding).mp hint4
  have hint_y := integrableOn_setIntegral_left hint_prod
  refine IntegrableOn.congr_fun hint_y ?_
    (cell3Set_isClosed knd _ _ _ _ _ _).measurableSet
  intro y hy; dsimp only
  have hmem : y 0 ∈ Icc A_R B_R ∧ y 1 ∈ Icc A_R B_R ∧ y 2 ∈ Icc A_R B_R := by
    have hA0r : A_R ≤ (n0a : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast hA0) (le_of_lt hDx)
    have h0Br : (n0b : ℝ) / D_x ≤ B_R := div_le_div_of_nonneg_right (by exact_mod_cast h0B) (le_of_lt hDx)
    have hA1r : A_R ≤ (n1a : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast hA1) (le_of_lt hDx)
    have h1Br : (n1b : ℝ) / D_x ≤ B_R := div_le_div_of_nonneg_right (by exact_mod_cast h1B) (le_of_lt hDx)
    have hA2r : A_R ≤ (n2a : ℝ) / D_x := div_le_div_of_nonneg_right (by exact_mod_cast hA2) (le_of_lt hDx)
    have h2Br : (n2b : ℝ) / D_x ≤ B_R := div_le_div_of_nonneg_right (by exact_mod_cast h2B) (le_of_lt hDx)
    cases knd with
    | box => exact ⟨⟨le_trans hA0r hy.1.1, le_trans hy.1.2 h0Br⟩, ⟨le_trans hA1r hy.2.1.1, le_trans hy.2.1.2 h1Br⟩, ⟨le_trans hA2r hy.2.2.1, le_trans hy.2.2.2 h2Br⟩⟩
    | tri01 => exact ⟨⟨le_trans hA0r hy.1.1, le_trans hy.1.2 h0Br⟩, ⟨le_trans hA0r hy.2.1.1, le_trans hy.2.1.2 h0Br⟩, ⟨le_trans hA2r hy.2.2.1.1, le_trans hy.2.2.1.2 h2Br⟩⟩
    | tri12 => exact ⟨⟨le_trans hA0r hy.1.1, le_trans hy.1.2 h0Br⟩, ⟨le_trans hA1r hy.2.1.1, le_trans hy.2.1.2 h1Br⟩, ⟨le_trans hA1r hy.2.2.1.1, le_trans hy.2.2.1.2 h1Br⟩⟩
    | simp => exact ⟨⟨le_trans hA0r hy.1.1, le_trans hy.1.2 h0Br⟩, ⟨le_trans hA0r hy.2.1.1, le_trans hy.2.1.2 h0Br⟩, ⟨le_trans hA0r hy.2.2.1.1, le_trans hy.2.2.1.2 h0Br⟩⟩
  have hy0 : 0 < y 0 := lt_of_lt_of_le (hA_pos hp) hmem.1.1
  have hy1 : 0 < y 1 := lt_of_lt_of_le (hA_pos hp) hmem.2.1.1
  have hy2 : 0 < y 2 := lt_of_lt_of_le (hA_pos hp) hmem.2.2.1
  set m := max B_R (min C_R (φ - y 0 - y 1 - 2 * y 2))
  have hBm : B_R ≤ m := le_max_left _ _
  have hmC : m ≤ C_R := max_le (le_of_lt (hBC_lt hp)) (min_le_left _ _)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt (hBC_lt hp))]
  have hsplit_int : IntervalIntegrable (fun x3 => g (x3, y)) volume B_R C_R := by
    have hPm : MeasurableSet {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} := measurableSet_Iic
    have heq_ind : ∀ x3 ∈ Icc B_R C_R, g (x3, y) =
        ({x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2}).indicator
          (fun x3 => (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3)))) x3 := by
      intro x3 hx3; dsimp only [g]
      by_cases hle : x3 ≤ φ - y 0 - y 1 - 2 * y 2
      · rw [Set.indicator_of_mem (show x3 ∈ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from hle)]
        have hu1 : 1 ≤ (φ - (y 0 + y 1 + y 2 + x3)) / y 2 := (one_le_div hy2).mpr (by linarith)
        have hu2 : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 ≤ 2 := (div_le_iff₀ hy2).mpr (by linarith [hmem.1.1, hmem.2.1.1, hmem.2.2.1, hx3.1])
        rw [hω.2.1 _ hu1 hu2]
        have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
        have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by linarith
        have hrem' : φ - (y 0 + y 1 + y 2 + x3) = φ - (y 0 + y 1 + y 2) - x3 := by ring
        rw [hrem']; field_simp [ne_of_gt hy0, ne_of_gt hy1, ne_of_gt hy2, ne_of_gt hx3p, ne_of_gt hrem]
      · rw [Set.indicator_of_notMem (show x3 ∉ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from hle)]
        have hlt : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 < 1 := (div_lt_one hy2).mpr (by linarith)
        rw [hω.2.2.2 _ hlt, zero_div]
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt (hBC_lt hp))).mpr ?_
    rw [integrableOn_congr_fun heq_ind measurableSet_Icc, integrableOn_indicator_iff hPm, inter_comm]
    have hcont_sub : ContinuousOn (fun x3 => (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3))))
        (Icc B_R C_R ∩ {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2}) := by
      refine continuousOn_const.mul (continuousOn_const.div (by fun_prop) ?_)
      intro x3 ⟨hx3, hle⟩
      have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
      have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by change x3 ≤ _ at hle; linarith
      positivity
    exact hcont_sub.integrableOn_compact (isCompact_Icc.inter_right (show IsClosed {x3 : ℝ | x3 ≤ φ - y 0 - y 1 - 2 * y 2} from isClosed_Iic))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hsplit_int.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le (le_of_lt (hBC_lt hp))]; exact ⟨hBm, hmC⟩)))
    (hsplit_int.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le (le_of_lt (hBC_lt hp))]; exact ⟨hBm, hmC⟩)))]
  have hright_zero : ∫ x3 in m..C_R, g (x3, y) = 0 := by
    rw [intervalIntegral.integral_of_le hmC]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x3 hx3
    have hgt : φ - y 0 - y 1 - 2 * y 2 < x3 := by
      by_cases hmc : m = C_R
      · exfalso; linarith [hx3.1, hx3.2]
      · have hlt_c : φ - y 0 - y 1 - 2 * y 2 < C_R := by
          by_contra hge; push Not at hge
          exact hmc (by dsimp only [m]; rw [min_eq_left hge, max_eq_right (le_of_lt (hBC_lt hp))])
        have : φ - y 0 - y 1 - 2 * y 2 ≤ m := by dsimp only [m]; rw [min_eq_right (le_of_lt hlt_c)]; exact le_max_right _ _
        linarith [hx3.1]
    have hlt : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 < 1 := (div_lt_one hy2).mpr (by linarith)
    dsimp only [g]; rw [hω.2.2.2 _ hlt, zero_div]
  rw [hright_zero, add_zero]
  by_cases hmB : m = B_R
  · unfold Buchstab4DT.G_fn; dsimp only [m] at hmB ⊢; rw [hmB]; simp
  · have hleft_eq : ∀ x3 ∈ uIcc B_R m, g (x3, y) =
        (1 / (y 0 * y 1 * y 2)) * (1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3))) := by
      intro x3 hx3; rw [uIcc_of_le hBm] at hx3
      have hle_cut : x3 ≤ φ - y 0 - y 1 - 2 * y 2 := by
        have : m = min C_R (φ - y 0 - y 1 - 2 * y 2) :=
          max_eq_right (by by_contra hlt; push Not at hlt; exact hmB (max_eq_left (le_of_lt hlt)))
        have : m ≤ φ - y 0 - y 1 - 2 * y 2 := by rw [this]; exact min_le_right _ _
        linarith [hx3.2]
      dsimp only [g]
      have hu1 : 1 ≤ (φ - (y 0 + y 1 + y 2 + x3)) / y 2 := (one_le_div hy2).mpr (by linarith)
      have hu2 : (φ - (y 0 + y 1 + y 2 + x3)) / y 2 ≤ 2 := (div_le_iff₀ hy2).mpr (by linarith [hmem.1.1, hmem.2.1.1, hmem.2.2.1, hx3.1])
      rw [hω.2.1 _ hu1 hu2]
      have hx3p : 0 < x3 := lt_of_lt_of_le (lt_trans (hA_pos hp) (hAB_lt hp)) hx3.1
      have hrem : 0 < φ - (y 0 + y 1 + y 2) - x3 := by linarith
      have hrem' : φ - (y 0 + y 1 + y 2 + x3) = φ - (y 0 + y 1 + y 2) - x3 := by ring
      rw [hrem']; field_simp [ne_of_gt hy0, ne_of_gt hy1, ne_of_gt hy2, ne_of_gt hx3p, ne_of_gt hrem]
    rw [intervalIntegral.integral_congr hleft_eq, intervalIntegral.integral_const_mul]; rfl

-- Helper: exact additivity of setIntegral on cell3Set splits (for signed integrable functions!)
lemma evalTree3_sound {F : (Fin 3 → ℝ) → ℝ}
    (hF_int : ∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid knd n0a n0b n1a n1b n2a n2b →
      IntegrableOn F (cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x)) volume)
    (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat)
    (hlf : ∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid knd n0a n0b n1a n1b n2a n2b →
      let r := lfFn knd n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / S_3)
    (t : BoxTree3) :
    ∀ (knd : CellKind) (n0a n0b n1a n1b n2a n2b : ℕ),
      tree3Valid knd t = true →
      cell3Valid knd n0a n0b n1a n1b n2a n2b →
      let r := evalTree3 lfFn knd t n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / D_x) ((n0b : ℝ) / D_x) ((n1a : ℝ) / D_x) ((n1b : ℝ) / D_x) ((n2a : ℝ) / D_x) ((n2b : ℝ) / D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / S_3 := by
  have hDx := (hDx_pos hp)
  have hdisj_coord : ∀ (A B : Set (Fin 3 → ℝ)) (i : Fin 3) (m : ℝ),
      (∀ x ∈ A ∩ B, x i = m) → AEDisjoint volume A B := fun A B i m h =>
    measure_mono_null h (volume_fin3_coord_eq_zero i m)
  induction t with
  | lf => intro knd a0 b0 a1 b1 a2 b2 _ hv; exact hlf knd a0 b0 a1 b1 a2 b2 hv
  | s0 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    set m := (a0 + b0) / 2
    rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, ht12, hts⟩
    have hml : a0 ≤ m := by omega
    have hmr : m ≤ b0 := by omega
    cases knd with
    | box =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      have hvl : cell3Valid .box a0 m a1 b1 a2 b2 := ⟨hA0, hml, le_trans hmr h0B, hA1, h1le, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩
      have hvr : cell3Valid .box m b0 a1 b1 a2 b2 := ⟨le_trans hA0 hml, hmr, h0B, hA1, h1le, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩
      have heq : cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) =
          cell3Set .box ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ∪
          cell3Set .box ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) := by
        ext x; constructor
        · intro hx; rcases le_total (x 0) ((m : ℝ) / D_x) with h | h
          · left; exact ⟨⟨hx.1.1, h⟩, hx.2⟩
          · right; exact ⟨⟨h, hx.1.2⟩, hx.2⟩
        · rintro (hx | hx)
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2⟩
          · exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.1.1, hx.1.2⟩, hx.2⟩
      have hsum := setIntegral_union₀ (hdisj_coord _ _ 0 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.1.2 h2.1.1))
        (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvl) (hF_int _ _ _ _ _ _ _ hvr)
      rw [heq, hsum]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ihl .box a0 m a1 b1 a2 b2 htv.1 hvl; have h2 := ihr .box m b0 a1 b1 a2 b2 htv.2 hvr; simp only [sub_div] at h1 h2; linarith only [h1, h2]
    | tri12 =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      rcases ht12 rfl with ⟨rfl, rfl⟩
      have hvl : cell3Valid .tri12 a0 m a1 b1 a1 b1 := ⟨hA0, hml, le_trans hmr h0B, hA1, h1le, h1B, hA1, h1le, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩
      have hvr : cell3Valid .tri12 m b0 a1 b1 a1 b1 := ⟨le_trans hA0 hml, hmr, h0B, hA1, h1le, h1B, hA1, h1le, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩
      have heq : cell3Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) =
          cell3Set .tri12 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ∪
          cell3Set .tri12 ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) := by
        ext x; constructor
        · intro hx; rcases le_total (x 0) ((m : ℝ) / D_x) with h | h
          · left; exact ⟨⟨hx.1.1, h⟩, hx.2⟩
          · right; exact ⟨⟨h, hx.1.2⟩, hx.2⟩
        · rintro (hx | hx)
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2⟩
          · exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.1.1, hx.1.2⟩, hx.2⟩
      have hsum := setIntegral_union₀ (hdisj_coord _ _ 0 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.1.2 h2.1.1))
        (cell3Set_isClosed .tri12 _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvl) (hF_int _ _ _ _ _ _ _ hvr)
      rw [heq, hsum]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ihl .tri12 a0 m a1 b1 a1 b1 htv.1 hvl; have h2 := ihr .tri12 m b0 a1 b1 a1 b1 htv.2 hvr; simp only [sub_div] at h1 h2; linarith only [h1, h2]
    | _ => simp [tree3Valid] at htv
  | s1 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    set m := (a1 + b1) / 2
    rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, _, _, _⟩
    have hml : a1 ≤ m := by omega
    have hmr : m ≤ b1 := by omega
    cases knd with
    | box =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      have hvl : cell3Valid .box a0 b0 a1 m a2 b2 := ⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩
      have hvr : cell3Valid .box a0 b0 m b1 a2 b2 := ⟨hA0, h0le, h0B, le_trans hA1 hml, hmr, h1B, hA2, h2le, h2B, by simp, by simp, by simp⟩
      have heq : cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) =
          cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) ∪
          cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) := by
        ext x; constructor
        · intro hx; rcases le_total (x 1) ((m : ℝ) / D_x) with h | h
          · left; exact ⟨hx.1, ⟨hx.2.1.1, h⟩, hx.2.2⟩
          · right; exact ⟨hx.1, ⟨h, hx.2.1.2⟩, hx.2.2⟩
        · rintro (hx | hx)
          · exact ⟨hx.1, ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2.2⟩
          · exact ⟨hx.1, ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩, hx.2.2⟩
      have hsum := setIntegral_union₀ (hdisj_coord _ _ 1 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.2.1.2 h2.2.1.1))
        (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvl) (hF_int _ _ _ _ _ _ _ hvr)
      rw [heq, hsum]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ihl .box a0 b0 a1 m a2 b2 htv.1 hvl; have h2 := ihr .box a0 b0 m b1 a2 b2 htv.2 hvr; simp only [sub_div] at h1 h2; linarith only [h1, h2]
    | _ => simp [tree3Valid] at htv
  | s2 l r ihl ihr =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    set m := (a2 + b2) / 2
    rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, h2le, h2B, ht01, _, _⟩
    have hml : a2 ≤ m := by omega
    have hmr : m ≤ b2 := by omega
    cases knd with
    | box =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      have hvl : cell3Valid .box a0 b0 a1 b1 a2 m := ⟨hA0, h0le, h0B, hA1, h1le, h1B, hA2, hml, le_trans hmr h2B, by simp, by simp, by simp⟩
      have hvr : cell3Valid .box a0 b0 a1 b1 m b2 := ⟨hA0, h0le, h0B, hA1, h1le, h1B, le_trans hA2 hml, hmr, h2B, by simp, by simp, by simp⟩
      have heq : cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) =
          cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((m : ℝ) / D_x) ∪
          cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((m : ℝ) / D_x) ((b2 : ℝ) / D_x) := by
        ext x; constructor
        · intro hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h | h
          · left; exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1, h⟩⟩
          · right; exact ⟨hx.1, hx.2.1, ⟨h, hx.2.2.2⟩⟩
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1, le_trans hx.2.2.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩⟩
          · exact ⟨hx.1, hx.2.1, ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1, hx.2.2.2⟩⟩
      have hsum := setIntegral_union₀ (hdisj_coord _ _ 2 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.2.2.2 h2.2.2.1))
        (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvl) (hF_int _ _ _ _ _ _ _ hvr)
      rw [heq, hsum]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ihl .box a0 b0 a1 b1 a2 m htv.1 hvl; have h2 := ihr .box a0 b0 a1 b1 m b2 htv.2 hvr; simp only [sub_div] at h1 h2; linarith only [h1, h2]
    | tri01 =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      rcases ht01 rfl with ⟨rfl, rfl⟩
      have hvl : cell3Valid .tri01 a0 b0 a0 b0 a2 m := ⟨hA0, h0le, h0B, hA0, h0le, h0B, hA2, hml, le_trans hmr h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩
      have hvr : cell3Valid .tri01 a0 b0 a0 b0 m b2 := ⟨hA0, h0le, h0B, hA0, h0le, h0B, le_trans hA2 hml, hmr, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩
      have heq : cell3Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) =
          cell3Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((m : ℝ) / D_x) ∪
          cell3Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b2 : ℝ) / D_x) := by
        ext x; constructor
        · intro hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h | h
          · left; exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1.1, h⟩, hx.2.2.2⟩
          · right; exact ⟨hx.1, hx.2.1, ⟨h, hx.2.2.1.2⟩, hx.2.2.2⟩
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.1, ⟨hx.2.2.1.1, le_trans hx.2.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2.2.2⟩
          · exact ⟨hx.1, hx.2.1, ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1.1, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hsum := setIntegral_union₀ (hdisj_coord _ _ 2 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.2.2.1.2 h2.2.2.1.1))
        (cell3Set_isClosed .tri01 _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvl) (hF_int _ _ _ _ _ _ _ hvr)
      rw [heq, hsum]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ihl .tri01 a0 b0 a0 b0 a2 m htv.1 hvl; have h2 := ihr .tri01 a0 b0 a0 b0 m b2 htv.2 hvr; simp only [sub_div] at h1 h2; linarith only [h1, h2]
    | _ => simp [tree3Valid] at htv
  | sd01 c0 mm c1 ih0 ihm ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    cases knd with
    | tri01 =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨hA0, h0le, h0B, _, _, _, hA2, h2le, h2B, ht01, _, _⟩
      rcases ht01 rfl with ⟨rfl, rfl⟩
      set m := (a0 + b0) / 2
      have hml : a0 ≤ m := by omega
      have hmr : m ≤ b0 := by omega
      have hv0 : cell3Valid .tri01 a0 m a0 m a2 b2 := ⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, hA2, h2le, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩
      have hvm : cell3Valid .box a0 m m b0 a2 b2 := ⟨hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, hA2, h2le, h2B, by simp, by simp, by simp⟩
      have hv1 : cell3Valid .tri01 m b0 m b0 a2 b2 := ⟨le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, hA2, h2le, h2B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩
      set S0 := cell3Set .tri01 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x)
      set Sm := cell3Set .box ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x)
      set S1 := cell3Set .tri01 ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x)
      have heq : cell3Set .tri01 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a2 : ℝ) / D_x) ((b2 : ℝ) / D_x) = S0 ∪ (Sm ∪ S1) := by
        ext x; constructor
        · intro hx; rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
          · left; exact ⟨⟨hx.1.1, le_trans hx.2.2.2 h1m⟩, ⟨hx.2.1.1, h1m⟩, hx.2.2⟩
          · right; rcases le_total (x 0) ((m : ℝ) / D_x) with h0m | h0m
            · left; exact ⟨⟨hx.1.1, h0m⟩, ⟨h1m, hx.2.1.2⟩, hx.2.2.1⟩
            · right; exact ⟨⟨h0m, hx.1.2⟩, ⟨h1m, hx.2.1.2⟩, hx.2.2⟩
        · rintro (hx | hx | hx)
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2.2⟩
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩,
                   hx.2.2, le_trans hx.1.2 hx.2.1.1⟩
          · exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.1.1, hx.1.2⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩, hx.2.2⟩
      have hd1 : AEDisjoint volume Sm S1 := hdisj_coord _ _ 0 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.1.2 h2.1.1)
      have hd0 : AEDisjoint volume S0 (Sm ∪ S1) := hdisj_coord _ _ 1 ((m : ℝ) / D_x) (fun x ⟨h0x, h1x⟩ => by
        rcases h1x with h | h; exact le_antisymm h0x.2.1.2 h.2.1.1; exact le_antisymm h0x.2.1.2 h.2.1.1)
      have hs1 := setIntegral_union₀ hd1 (cell3Set_isClosed .tri01 _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvm) (hF_int _ _ _ _ _ _ _ hv1)
      have hs0 := setIntegral_union₀ hd0 ((cell3Set_isClosed .box _ _ _ _ _ _).measurableSet.union (cell3Set_isClosed .tri01 _ _ _ _ _ _).measurableSet).nullMeasurableSet
        (hF_int _ _ _ _ _ _ _ hv0) ((hF_int _ _ _ _ _ _ _ hvm).union (hF_int _ _ _ _ _ _ _ hv1))
      rw [heq, hs0, hs1]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ih0 .tri01 a0 m a0 m a2 b2 htv.1.1 hv0; have h2 := ihm .box a0 m m b0 a2 b2 htv.1.2 hvm; have h3 := ih1 .tri01 m b0 m b0 a2 b2 htv.2 hv1; simp only [sub_div] at h1 h2 h3; linarith only [h1, h2, h3]
    | _ => simp [tree3Valid] at htv
  | sd12 c0 mm c1 ih0 ihm ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    cases knd with
    | tri12 =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨hA0, h0le, h0B, hA1, h1le, h1B, _, _, _, _, ht12, _⟩
      rcases ht12 rfl with ⟨rfl, rfl⟩
      set m := (a1 + b1) / 2
      have hml : a1 ≤ m := by omega
      have hmr : m ≤ b1 := by omega
      have hv0 : cell3Valid .tri12 a0 b0 a1 m a1 m := ⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, hA1, hml, le_trans hmr h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩
      have hvm : cell3Valid .box a0 b0 a1 m m b1 := ⟨hA0, h0le, h0B, hA1, hml, le_trans hmr h1B, le_trans hA1 hml, hmr, h1B, by simp, by simp, by simp⟩
      have hv1 : cell3Valid .tri12 a0 b0 m b1 m b1 := ⟨hA0, h0le, h0B, le_trans hA1 hml, hmr, h1B, le_trans hA1 hml, hmr, h1B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩
      set S0 := cell3Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x)
      set Sm := cell3Set .box ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x)
      set S1 := cell3Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x) ((m : ℝ) / D_x) ((b1 : ℝ) / D_x)
      have heq : cell3Set .tri12 ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) ((a1 : ℝ) / D_x) ((b1 : ℝ) / D_x) = S0 ∪ (Sm ∪ S1) := by
        ext x; constructor
        · intro hx; rcases le_total (x 2) ((m : ℝ) / D_x) with h2m | h2m
          · left; exact ⟨hx.1, ⟨hx.2.1.1, le_trans hx.2.2.2 h2m⟩, ⟨hx.2.2.1.1, h2m⟩, hx.2.2.2⟩
          · right; rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
            · left; exact ⟨hx.1, ⟨hx.2.1.1, h1m⟩, ⟨h2m, hx.2.2.1.2⟩⟩
            · right; exact ⟨hx.1, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2⟩
        · rintro (hx | hx | hx)
          · exact ⟨hx.1, ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨hx.2.2.1.1, le_trans hx.2.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2.2.2⟩
          · exact ⟨hx.1, ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1, hx.2.2.2⟩,
                   le_trans hx.2.1.2 hx.2.2.1⟩
          · exact ⟨hx.1, ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1.1, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hd1 : AEDisjoint volume Sm S1 := hdisj_coord _ _ 1 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.2.1.2 h2.2.1.1)
      have hd0 : AEDisjoint volume S0 (Sm ∪ S1) := hdisj_coord _ _ 2 ((m : ℝ) / D_x) (fun x ⟨h0x, h1x⟩ => by
        rcases h1x with h | h; exact le_antisymm h0x.2.2.1.2 h.2.2.1; exact le_antisymm h0x.2.2.1.2 h.2.2.1.1)
      have hs1 := setIntegral_union₀ hd1 (cell3Set_isClosed .tri12 _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hvm) (hF_int _ _ _ _ _ _ _ hv1)
      have hs0 := setIntegral_union₀ hd0 ((cell3Set_isClosed .box _ _ _ _ _ _).measurableSet.union (cell3Set_isClosed .tri12 _ _ _ _ _ _).measurableSet).nullMeasurableSet
        (hF_int _ _ _ _ _ _ _ hv0) ((hF_int _ _ _ _ _ _ _ hvm).union (hF_int _ _ _ _ _ _ _ hv1))
      rw [heq, hs0, hs1]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ih0 .tri12 a0 b0 a1 m a1 m htv.1.1 hv0; have h2 := ihm .box a0 b0 a1 m m b1 htv.1.2 hvm; have h3 := ih1 .tri12 a0 b0 m b1 m b1 htv.2 hv1; simp only [sub_div] at h1 h2 h3; linarith only [h1, h2, h3]
    | _ => simp [tree3Valid] at htv
  | sd012 c0 m01 m12 c1 ih0 ih01 ih12 ih1 =>
    intro knd a0 b0 a1 b1 a2 b2 htv hv
    cases knd with
    | simp =>
      simp only [tree3Valid, Bool.and_eq_true] at htv
      rcases hv with ⟨hA0, h0le, h0B, _, _, _, _, _, _, _, _, hts⟩
      rcases hts rfl with ⟨rfl, rfl, rfl, rfl⟩
      set m := (a0 + b0) / 2
      have hml : a0 ≤ m := by omega
      have hmr : m ≤ b0 := by omega
      have hv0 : cell3Valid .simp a0 m a0 m a0 m := ⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, by simp, by simp, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
      have hv01 : cell3Valid .tri01 a0 m a0 m m b0 := ⟨hA0, hml, le_trans hmr h0B, hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, fun _ => ⟨rfl, rfl⟩, by simp, by simp⟩
      have hv12 : cell3Valid .tri12 a0 m m b0 m b0 := ⟨hA0, hml, le_trans hmr h0B, le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, by simp, fun _ => ⟨rfl, rfl⟩, by simp⟩
      have hv1 : cell3Valid .simp m b0 m b0 m b0 := ⟨le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, le_trans hA0 hml, hmr, h0B, by simp, by simp, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
      set S0 := cell3Set .simp ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x)
      set S01 := cell3Set .tri01 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x)
      set S12 := cell3Set .tri12 ((a0 : ℝ) / D_x) ((m : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x)
      set S1 := cell3Set .simp ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x) ((m : ℝ) / D_x) ((b0 : ℝ) / D_x)
      have heq : cell3Set .simp ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) ((a0 : ℝ) / D_x) ((b0 : ℝ) / D_x) = S0 ∪ (S01 ∪ (S12 ∪ S1)) := by
        ext x; constructor
        · intro hx
          rcases le_total (x 2) ((m : ℝ) / D_x) with h2m | h2m
          · left; exact ⟨⟨hx.1.1, le_trans hx.2.2.2.1 (le_trans hx.2.2.2.2 h2m)⟩, ⟨hx.2.1.1, le_trans hx.2.2.2.2 h2m⟩, ⟨hx.2.2.1.1, h2m⟩, hx.2.2.2⟩
          · right; rcases le_total (x 1) ((m : ℝ) / D_x) with h1m | h1m
            · left; exact ⟨⟨hx.1.1, le_trans hx.2.2.2.1 h1m⟩, ⟨hx.2.1.1, h1m⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2.1⟩
            · right; rcases le_total (x 0) ((m : ℝ) / D_x) with h0m | h0m
              · left; exact ⟨⟨hx.1.1, h0m⟩, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2.2⟩
              · right; exact ⟨⟨h0m, hx.1.2⟩, ⟨h1m, hx.2.1.2⟩, ⟨h2m, hx.2.2.1.2⟩, hx.2.2.2⟩
        · rintro (hx | hx | hx | hx)
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨hx.2.2.1.1, le_trans hx.2.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩, hx.2.2.2⟩
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨hx.2.1.1, le_trans hx.2.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1.1, hx.2.2.1.2⟩,
                   hx.2.2.2, le_trans hx.2.1.2 hx.2.2.1.1⟩
          · exact ⟨⟨hx.1.1, le_trans hx.1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hmr) (le_of_lt hDx))⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1.1, hx.2.2.1.2⟩,
                   le_trans hx.1.2 hx.2.1.1, hx.2.2.2⟩
          · exact ⟨⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.1.1, hx.1.2⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.1.1, hx.2.1.2⟩,
                   ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hml) (le_of_lt hDx)) hx.2.2.1.1, hx.2.2.1.2⟩, hx.2.2.2⟩
      have hd2 : AEDisjoint volume S12 S1 := hdisj_coord _ _ 0 ((m : ℝ) / D_x) (fun x ⟨h1, h2⟩ => le_antisymm h1.1.2 h2.1.1)
      have hd1 : AEDisjoint volume S01 (S12 ∪ S1) := hdisj_coord _ _ 1 ((m : ℝ) / D_x) (fun x ⟨h0x, h1x⟩ => by
        rcases h1x with h | h; exact le_antisymm h0x.2.1.2 h.2.1.1; exact le_antisymm h0x.2.1.2 h.2.1.1)
      have hd0 : AEDisjoint volume S0 (S01 ∪ (S12 ∪ S1)) := hdisj_coord _ _ 2 ((m : ℝ) / D_x) (fun x ⟨h0x, h1x⟩ => by
        rcases h1x with h | h | h
        · exact le_antisymm h0x.2.2.1.2 h.2.2.1.1
        · exact le_antisymm h0x.2.2.1.2 h.2.2.1.1
        · exact le_antisymm h0x.2.2.1.2 h.2.2.1.1)
      have hs2 := setIntegral_union₀ hd2 (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet.nullMeasurableSet (hF_int _ _ _ _ _ _ _ hv12) (hF_int _ _ _ _ _ _ _ hv1)
      have hs1 := setIntegral_union₀ hd1 ((cell3Set_isClosed .tri12 _ _ _ _ _ _).measurableSet.union (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet).nullMeasurableSet
        (hF_int _ _ _ _ _ _ _ hv01) ((hF_int _ _ _ _ _ _ _ hv12).union (hF_int _ _ _ _ _ _ _ hv1))
      have hs0 := setIntegral_union₀ hd0
        ((cell3Set_isClosed .tri01 _ _ _ _ _ _).measurableSet.union ((cell3Set_isClosed .tri12 _ _ _ _ _ _).measurableSet.union (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet)).nullMeasurableSet
        (hF_int _ _ _ _ _ _ _ hv0) ((hF_int _ _ _ _ _ _ _ hv01).union ((hF_int _ _ _ _ _ _ _ hv12).union (hF_int _ _ _ _ _ _ _ hv1)))
      rw [heq, hs0, hs1, hs2]; simp only [evalTree3, addPair, Nat.cast_add, add_div, sub_div]
      have h1 := ih0 .simp a0 m a0 m a0 m htv.1.1.1 hv0; have h2 := ih01 .tri01 a0 m a0 m m b0 htv.1.1.2 hv01; have h3 := ih12 .tri12 a0 m m b0 m b0 htv.1.2 hv12; have h4 := ih1 .simp m b0 m b0 m b0 htv.2 hv1; simp only [sub_div] at h1 h2 h3 h4; linarith only [h1, h2, h3, h4]
    | _ => simp [tree3Valid] at htv


end

end Sol_Buchstab4DT_Sound4

theorem solution :
∀ (p : Params4DT), p.Valid →
  (∀ {dx0 dx1 dx2 r : ℕ},
    ((cut3Num p dx0 dx1 dx2 r : ℝ) / (12 * (p.D_p : ℝ) ^ 3 * (p.D_x : ℝ) ^ 3)) =
      cut3SumR ((dx0 : ℝ) / p.D_x) ((dx1 : ℝ) / p.D_x) (2 * ((dx2 : ℝ) / p.D_x)) ((r : ℝ) / ((p.D_p : ℝ) * p.D_x)) / 12) ∧
  (∀ {dx0 dx1 dx2 r : ℕ},
    ((ramp3Num p dx0 dx1 dx2 r : ℝ) / (48 * (p.D_p : ℝ) ^ 4 * (p.D_x : ℝ) ^ 4)) =
      ramp3SumR ((dx0 : ℝ) / p.D_x) ((dx1 : ℝ) / p.D_x) (2 * ((dx2 : ℝ) / p.D_x)) ((r : ℝ) / ((p.D_p : ℝ) * p.D_x)) / 48) ∧
  (∀ {knd n0a n0b n1a n1b n2a n2b}, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
    cell3Ok knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {p_n : ℕ}, (p_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    ∀ {knd n0a n0b n1a n1b n2a n2b n3a n3b}, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
    ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                        ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
      ω (((p_n : ℝ) / p.D_p - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4Leaf p p_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {pa_n : ℕ} {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ →
    p.D_p * (4 * p.B_n + p.C_n) ≤ pa_n * p.D_x →
    ∀ {knd n0a n0b n1a n1b n2a n2b n3a n3b}, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
    ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                        ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
      ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4TransLeaf p pa_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω →
    ∀ (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) (φ : ℝ),
    (∀ knd n0a n0b n1a n1b n2a n2b n3a n3b, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                          ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (lfFn knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) →
    ∀ (t : BoxTree4) (knd : CellKind) (n0a n0b n1a n1b n2a n2b n3a n3b : ℕ),
      tree4Valid knd t = true → cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                          ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (evalTree4 lfFn knd t n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {φ : ℝ}, φ ≤ 5 * p.A_R + p.B_R →
    I_fn p ω φ = ∫ y in cell3Set .simp p.A_R p.B_R p.A_R p.B_R p.A_R p.B_R,
      (1 / (y 0 * y 1 * y 2)) * G_fn p φ y) ∧
  (∀ {φ1 φ2 : ℝ}, φ1 < φ2 → ∀ {y : Fin 3 → ℝ}, 0 < y 2 →
    let m1 := max p.B_R (min p.C_R (φ1 - y 0 - y 1 - 2 * y 2))
    let m2 := max p.B_R (min p.C_R (φ2 - y 0 - y 1 - 2 * y 2))
    G_fn p φ2 y - G_fn p φ1 y =
      (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) -
      (φ2 - φ1) * (∫ x3 in p.B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)))) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {φ : ℝ}, φ ≤ 5 * p.A_R + p.B_R →
    ∀ {knd n0a n0b n1a n1b n2a n2b}, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
    IntegrableOn (fun y : Fin 3 → ℝ => (1 / (y 0 * y 1 * y 2)) * G_fn p φ y)
      (cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) volume) ∧
  (∀ {F : (Fin 3 → ℝ) → ℝ},
    (∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      IntegrableOn F (cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) volume) →
    ∀ (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat),
    (∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      let r := lfFn knd n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / p.S_3) →
    ∀ (t : BoxTree3) (knd : CellKind) (n0a n0b n1a n1b n2a n2b : ℕ),
      tree3Valid knd t = true → cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      let r := evalTree3 lfFn knd t n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / p.S_3) := fun p hp =>
  ⟨@Sol_Buchstab4DT_Sound4.cut3Num_eq p hp,
   @Sol_Buchstab4DT_Sound4.ramp3Num_eq p hp,
   @Sol_Buchstab4DT_Sound4.cell3Valid_ok p hp,
   @Sol_Buchstab4DT_Sound4.cell4_leaf_sound p hp,
   @Sol_Buchstab4DT_Sound4.cell4_trans_leaf_sound p hp,
   @Sol_Buchstab4DT_Sound4.evalTree4_sound p hp,
   @Sol_Buchstab4DT_Sound4.I_fn_eq_G p hp,
   @Sol_Buchstab4DT_Sound4.G_fn_sub_eq p hp,
   @Sol_Buchstab4DT_Sound4.G_fn_integrableOn p hp,
   @Sol_Buchstab4DT_Sound4.evalTree3_sound p hp⟩
