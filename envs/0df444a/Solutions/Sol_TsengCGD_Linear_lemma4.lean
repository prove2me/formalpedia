-- Prove2me | solution 1 for TsengCGD.Linear.lemma4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:03:42.698235+00:00
-- url     : https://prove2.me/submissions/317ca7fa-636c-495d-aefe-a072655c1678

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace


namespace TsengCGD.Linear

open TsengCGD.Global

lemma g37b_line_deriv {n : ℕ} (h : Vec n → ℝ) (x v : Vec n) (t : ℝ)
    (hd : DifferentiableAt ℝ h (x + t • v)) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := hd.hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma g37_inner_supp' {n : ℕ} (J : Finset (Fin n)) (g v : Vec n) (hv : SupportedOn J v) :
    ⟪g, v⟫ = ∑ j ∈ J, g j * v j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  · apply Finset.sum_congr rfl; intro j _; ring
  · intro j _ hj; rw [hv j hj]; ring

lemma g37b_fo {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ} {h : Vec n → ℝ}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hh : Differentiable ℝ h)
    {x : Vec n} {J : Finset (Fin n)} {g d : Vec n}
    (hd : SupportedOn J d ∧ x + d ∈ D ∧ ∀ d', SupportedOn J d' → x + d' ∈ D →
      ⟪g, d⟫ + h d + c * P (x + d) ≤ ⟪g, d'⟫ + h d' + c * P (x + d'))
    (e : Vec n) (he : SupportedOn J e) (hxe : x + e ∈ D) :
    0 ≤ ⟪g, e - d⟫ + ⟪gradient h d, e - d⟫ + c * (P (x + e) - P (x + d)) := by
  obtain ⟨hdS, hdD, hdmin⟩ := hd
  set v := e - d with hv
  set A := ⟪g, v⟫ + c * (P (x + e) - P (x + d)) with hA
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + (h (d + s • v) - h d) / s := by
    intro s hs0 hs1
    have hsup : SupportedOn J (d + s • v) := by
      intro j hj; simp [hv, hdS j hj, he j hj]
    have hmemE : x + (d + s • v) = (1 - s) • (x + d) + s • (x + e) := by rw [hv]; module
    have hmem : x + (d + s • v) ∈ D := by
      rw [hmemE]; exact hD hdD hxe (by linarith) hs0.le (by ring)
    have h1 := hdmin _ hsup hmem
    have hP := hPc.2 hdD hxe (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
    simp only [smul_eq_mul] at hP
    rw [← hmemE] at hP
    rw [inner_add_right, inner_smul_right] at h1
    have h2 := mul_le_mul_of_nonneg_left hP hc
    have h3 : 0 ≤ s * A + (h (d + s • v) - h d) := by rw [hA]; nlinarith
    have h4 : (h (d + s • v) - h d) / s * s = h (d + s • v) - h d := by field_simp
    have h5 : 0 ≤ s * (A + (h (d + s • v) - h d) / s) := by nlinarith
    exact (mul_nonneg_iff_of_pos_left hs0).mp h5
  have hder := g37b_line_deriv h d v 0 (hh _)
  simp only [zero_smul, add_zero] at hder
  have hsl := hasDerivAt_iff_tendsto_slope.mp hder
  have hsl' : Tendsto (slope (fun s : ℝ => h (d + s • v)) 0) (𝓝[>] 0) (𝓝 ⟪gradient h d, v⟫) :=
    hsl.mono_left (nhdsWithin_mono _ (fun s hs => ne_of_gt hs))
  have hlim : Tendsto (fun s => A + slope (fun s : ℝ => h (d + s • v)) 0 s) (𝓝[>] 0)
      (𝓝 (A + ⟪gradient h d, v⟫)) := hsl'.const_add A
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 ≤ A + slope (fun s : ℝ => h (d + s • v)) 0 s := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
    rw [slope_def_field]
    simp only [zero_smul, add_zero, sub_zero]
    exact key s hs.1 hs.2.le
  have := ge_of_tendsto hlim hev
  rw [hA] at this; linarith

theorem lemma4_core {n : ℕ} (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c)
    (h : TsengCGD.Global.Vec n → ℝ) (hh : ContDiff ℝ 1 h) (ρ p q : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (hq : 1 / p + 1 / q = 1)
    (hmono : ∀ u v : TsengCGD.Global.Vec n, ρ * pNorm p (u - v) ^ p ≤ ⟪gradient h u - gradient h v, u - v⟫)
    (x : TsengCGD.Global.Vec n) (J : Finset (Fin n)) (gb gt db dt : TsengCGD.Global.Vec n)
    (hdb : TsengCGD.Global.SupportedOn J db ∧ x + db ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gb, db⟫ + h db + c * P (x + db) ≤ ⟪gb, d'⟫ + h d' + c * P (x + d'))
    (hdt : TsengCGD.Global.SupportedOn J dt ∧ x + dt ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gt, dt⟫ + h dt + c * P (x + dt) ≤ ⟪gt, d'⟫ + h d' + c * P (x + d')) :
    pNorm p (db - dt) ≤ ρ ^ (-q / p) * pNormOn q J (gb - gt) ^ (q / p) := by
  have hD : Convex ℝ D := hP.2.1
  have hPc : ConvexOn ℝ D P := hP.2.2.1
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have h1 := g37b_fo hD hPc hc.le hdiff hdb dt hdt.1 hdt.2.1
  have h2 := g37b_fo hD hPc hc.le hdiff hdt db hdb.1 hdb.2.1
  have hm := hmono db dt
  -- combine
  have hcomb : ρ * pNorm p (db - dt) ^ p ≤ ⟪gt - gb, db - dt⟫ := by
    have e1 : ⟪gb, dt - db⟫ = -⟪gb, db - dt⟫ := by rw [← inner_neg_right, neg_sub]
    have e2 : ⟪gradient h db, dt - db⟫ = -⟪gradient h db, db - dt⟫ := by rw [← inner_neg_right, neg_sub]
    rw [inner_sub_left] at hm ⊢
    linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by
    by_contra hcon
    push_neg at hcon
    have : 1 / q ≤ 0 := by
      rcases hcon.lt_or_eq with h' | h'
      · exact (one_div_neg.mpr h').le
      · rw [h']; simp
    have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]; refine ⟨hp, ?_⟩; simpa [one_div] using hq
  have hdS : SupportedOn J (db - dt) := by intro j hj; simp [hdb.1 j hj, hdt.1 j hj]
  set N := pNorm p (db - dt) with hN
  set G := pNormOn q J (gb - gt) with hG
  have hNsum : N = (∑ j ∈ J, |(db - dt) j| ^ p) ^ (1 / p) := by
    rw [hN, pNorm, ← Finset.sum_subset (Finset.subset_univ J)]
    intro j _ hj; rw [hdS j hj, abs_zero, Real.zero_rpow hp0.ne']
  have hhold : ⟪gt - gb, db - dt⟫ ≤ G * N := by
    rw [g37_inner_supp' J _ _ hdS]
    have := Real.inner_le_Lp_mul_Lq J (fun j => (gt - gb) j) (fun j => (db - dt) j) hpq.symm
    have eG : (∑ i ∈ J, |(gt - gb) i| ^ q) = ∑ i ∈ J, |(gb - gt) i| ^ q := by
      apply Finset.sum_congr rfl; intro j _; rw [← abs_neg]; simp
    rw [hG, pNormOn, ← eG, hNsum]
    exact this
  have hN0 : 0 ≤ N := by rw [hN, pNorm]; positivity
  have hG0 : 0 ≤ G := by rw [hG, pNormOn]; positivity
  -- exponent algebra
  have hqp : q / p * (p - 1) = 1 := by
    field_simp at hq ⊢; linarith
  have hRHS : ρ ^ (-q / p) * G ^ (q / p) = (G / ρ) ^ (q / p) := by
    rw [Real.div_rpow hG0 hρ.le, neg_div, Real.rpow_neg hρ.le]; ring
  rw [hRHS]
  rcases hN0.lt_or_eq with hNpos | hNz
  · have h3 : ρ * N ^ p ≤ G * N := le_trans hcomb hhold
    have h4 : N ^ p = N ^ (p - 1) * N := by
      rw [Real.rpow_sub_one hNpos.ne']; field_simp
    rw [h4] at h3
    have h5 : N ^ (p - 1) ≤ G / ρ := by
      rw [le_div_iff₀ hρ]; nlinarith
    have h6 : N = (N ^ (p - 1)) ^ (q / p) := by
      rw [← Real.rpow_mul hN0, mul_comm, hqp, Real.rpow_one]
    calc N = (N ^ (p - 1)) ^ (q / p) := h6
      _ ≤ (G / ρ) ^ (q / p) := Real.rpow_le_rpow (by positivity) h5 (by positivity)
  · rw [← hNz]; positivity

end TsengCGD.Linear

open TsengCGD.Linear


theorem solution {n : ℕ} (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c)
    (h : TsengCGD.Global.Vec n → ℝ) (hh : ContDiff ℝ 1 h) (ρ p q : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (hq : 1 / p + 1 / q = 1)
    (hmono : ∀ u v : TsengCGD.Global.Vec n, ρ * pNorm p (u - v) ^ p ≤ ⟪gradient h u - gradient h v, u - v⟫)
    (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty) (gb gt db dt : TsengCGD.Global.Vec n)
    (hdb : TsengCGD.Global.SupportedOn J db ∧ x + db ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gb, db⟫ + h db + c * P (x + db) ≤ ⟪gb, d'⟫ + h d' + c * P (x + d'))
    (hdt : TsengCGD.Global.SupportedOn J dt ∧ x + dt ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gt, dt⟫ + h dt + c * P (x + dt) ≤ ⟪gt, d'⟫ + h d' + c * P (x + d')) :
    pNorm p (db - dt) ≤ ρ ^ (-q / p) * pNormOn q J (gb - gt) ^ (q / p) := by
  exact lemma4_core D P c hP hc h hh ρ p q hρ hp hq hmono x J gb gt db dt hdb hdt
