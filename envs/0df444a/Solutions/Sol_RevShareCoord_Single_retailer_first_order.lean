-- Prove2me | solution 1 for RevShareCoord.Single.retailer_first_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:04:20.972835+00:00
-- url     : https://prove2.me/submissions/116a3c36-45de-4284-8062-63ab51e0e627

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model



namespace RevShareCoord.Single

open Set Filter Topology

lemma rs_sc_affine {f : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) f) {a b : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ici 0) (fun q => a * f q - q * b) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy s t hs ht hst
  have h := hc.2 hx hy hxy hs ht hst
  simp only [smul_eq_mul] at h ⊢
  have h2 : a * (s * f x + t * f y) < a * f (s * x + t * y) := mul_lt_mul_of_pos_left h ha
  have : t = 1 - s := by linarith
  subst this
  nlinarith

lemma rs_uniq {f : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) f) (q₁ q₂ : ℝ) (h1 : 0 ≤ q₁)
    (h2 : 0 ≤ q₂) (m1 : IsMaxOn f (Ici 0) q₁) (m2 : IsMaxOn f (Ici 0) q₂) : q₁ = q₂ := by
  by_contra hne
  have h := hc.2 (show q₁ ∈ Ici (0:ℝ) from h1) (show q₂ ∈ Ici (0:ℝ) from h2) hne
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have hm : (1/2 : ℝ) * q₁ + 1/2 * q₂ ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
  have a1 := m1 hm
  have a2 := m2 (show q₁ ∈ Ici (0:ℝ) from h1)
  have a3 := m1 (show q₂ ∈ Ici (0:ℝ) from h2)
  simp only [mem_setOf_eq] at a1 a2 a3
  linarith

lemma rs_iff {f g : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) f)
    (hd : ∀ q, 0 ≤ q → HasDerivWithinAt f (g q) (Ici 0) q) (h0 : 0 < g 0) (q : ℝ) (hq : 0 ≤ q) :
    IsMaxOn f (Ici 0) q ↔ 0 < q ∧ g q = 0 := by
  constructor
  · intro hm
    have hqpos : 0 < q := by
      rcases hq.lt_or_eq with h | h
      · exact h
      exfalso
      subst h
      have ht := (hasDerivWithinAt_iff_tendsto_slope.mp (hd 0 le_rfl))
      have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by
        ext x; simp [lt_iff_le_and_ne, eq_comm]
      rw [hset] at ht
      have hev : ∀ᶠ y in 𝓝[>] (0:ℝ), 0 < slope f 0 y :=
        ht.eventually (lt_mem_nhds h0)
      obtain ⟨y, hy, hy2⟩ := (hev.and (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0)).exists
      have hy0 : 0 < y := hy2
      have := hm (show y ∈ Ici (0:ℝ) from hy0.le)
      simp only [mem_setOf_eq] at this
      rw [slope_def_field] at hy
      have : (f y - f 0) / (y - 0) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      linarith
    refine ⟨hqpos, ?_⟩
    have hn : Ici (0:ℝ) ∈ 𝓝 q := Ici_mem_nhds hqpos
    have hD : HasDerivAt f (g q) q := (hd q hq).hasDerivAt hn
    exact (hm.isLocalMax hn).hasDerivAt_eq_zero hD
  · rintro ⟨hqpos, hg⟩ y hy
    simp only [mem_Ici] at hy
    simp only [mem_setOf_eq]
    rcases lt_trichotomy y q with h | h | h
    · have := hc.lt_slope_of_hasDerivWithinAt (show y ∈ Ici (0:ℝ) from hy)
        (show q ∈ Ici (0:ℝ) from hq) h (hd q hq)
      rw [hg, slope_def_field] at this
      have hpos : 0 < q - y := by linarith
      have := (div_pos_iff_of_pos_right hpos).mp this
      linarith
    · rw [h]
    · have := hc.slope_lt_of_hasDerivWithinAt (show q ∈ Ici (0:ℝ) from hq)
        (show y ∈ Ici (0:ℝ) from hy) h (hd q hq)
      rw [hg, slope_def_field] at this
      have hpos : 0 < y - q := by linarith
      by_contra hcon
      have : 0 < (f y - f q) / (y - q) := div_pos (by linarith) hpos
      linarith

lemma rs_exists {f g : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) f)
    (hd : ∀ q, 0 ≤ q → HasDerivWithinAt f (g q) (Ici 0) q) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : g Q < 0) :
    ∃ q, 0 ≤ q ∧ IsMaxOn f (Ici 0) q := by
  have cont : ContinuousOn f (Icc 0 Q) := fun x hx =>
    (hd x hx.1).continuousWithinAt.mono Icc_subset_Ici_self
  obtain ⟨q, hqmem, hqmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hQ0) cont
  refine ⟨q, hqmem.1, ?_⟩
  intro y hy
  simp only [mem_Ici] at hy
  simp only [mem_setOf_eq]
  rcases le_or_gt y Q with h | h
  · exact hqmax ⟨hy, h⟩
  · have := hc.slope_lt_of_hasDerivWithinAt (show Q ∈ Ici (0:ℝ) from hQ0)
        (show y ∈ Ici (0:ℝ) from hy) h (hd Q hQ0)
    rw [slope_def_field] at this
    have hpos : 0 < y - Q := by linarith
    have hfQ := hqmax (show Q ∈ Icc 0 Q from ⟨hQ0, le_rfl⟩)
    simp only [mem_setOf_eq] at hfQ
    by_contra hcon
    have : 0 < (f y - f Q) / (y - Q) := div_pos (by linarith) hpos
    linarith

lemma rs_hd (M : Model) (a b : ℝ) (q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => a * M.R q - q * b) (a * M.R' q - b) (Ici 0) q := by
  have h := ((M.hasDeriv q hq).const_mul a).sub ((hasDerivWithinAt_id q (Ici 0)).mul_const b)
  simp only [id, one_mul] at h
  exact h

lemma Pi_eq (M : Model) : M.Pi = fun q => 1 * M.R q - q * M.c := by
  funext q; simp [Model.Pi]

lemma ret_eq (M : Model) (φ w : ℝ) : M.retailerProfit φ w = fun q => φ * M.R q - q * w := by
  funext q; simp [Model.retailerProfit]

lemma Pi_sc (M : Model) : StrictConcaveOn ℝ (Ici 0) M.Pi := by
  rw [Pi_eq]; exact rs_sc_affine M.strictConcave one_pos

lemma Pi_iff (M : Model) (q : ℝ) (hq : 0 ≤ q) :
    IsMaxOn M.Pi (Ici 0) q ↔ 0 < q ∧ M.R' q = M.c := by
  rw [Pi_eq, rs_iff (rs_sc_affine M.strictConcave one_pos) (g := fun q => 1 * M.R' q - M.c)
    (fun q hq => rs_hd M 1 M.c q hq) (by simp; linarith [M.viable]) q hq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp at h2 ⊢; linarith⟩

theorem integrated_optimum_core (M : Model) :
    ∃ qI : ℝ, 0 < qI ∧ M.R' qI = M.c ∧ IsMaxOn M.Pi (Set.Ici 0) qI ∧
      (∀ q : ℝ, 0 ≤ q → IsMaxOn M.Pi (Set.Ici 0) q → q = qI) ∧
      (∀ q : ℝ, 0 < q → M.R' q = M.c → q = qI) := by
  obtain ⟨Q, hQ0, hQ⟩ := M.finite_optimal
  obtain ⟨qI, hqI0, hmax⟩ := rs_exists (Pi_sc M) (g := fun q => 1 * M.R' q - M.c)
    (fun q hq => by rw [Pi_eq]; exact rs_hd M 1 M.c q hq) Q hQ0 (by simp; linarith)
  obtain ⟨hpos, hR⟩ := (Pi_iff M qI hqI0).1 hmax
  refine ⟨qI, hpos, hR, hmax, ?_, ?_⟩
  · intro q hq hm; exact rs_uniq (Pi_sc M) q qI hq hqI0 hm hmax
  · intro q hq hR'
    exact rs_uniq (Pi_sc M) q qI hq.le hqI0 ((Pi_iff M q hq.le).2 ⟨hq, hR'⟩) hmax

theorem retailer_first_order_core (M : Model) (φ w : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w)
    (hR0 : w / φ < M.R' 0) :
    (∀ qhat : ℝ, 0 ≤ qhat →
      (IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qhat ↔ 0 < qhat ∧ φ * M.R' qhat = w)) ∧
    (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₁ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₂ → q₁ = q₂) := by
  have hsc := rs_sc_affine (b := w) M.strictConcave hφ0
  have h0 : 0 < φ * M.R' 0 - w := by
    rw [div_lt_iff₀ hφ0] at hR0; linarith
  rw [ret_eq]
  refine ⟨?_, fun q₁ q₂ h1 h2 m1 m2 => rs_uniq hsc q₁ q₂ h1 h2 m1 m2⟩
  intro qhat hq
  rw [rs_iff hsc (g := fun q => φ * M.R' q - w) (fun q hq => rs_hd M φ w q hq) h0 qhat hq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma ret_phi (M : Model) (φ : ℝ) : M.retailerProfit φ (φ * M.c) = fun q => φ * M.Pi q := by
  funext q; simp only [Model.retailerProfit, Model.Pi]; ring

lemma ret_max_iff (M : Model) (φ : ℝ) (hφ0 : 0 < φ) (q : ℝ) :
    IsMaxOn (M.retailerProfit φ (φ * M.c)) (Ici 0) q ↔ IsMaxOn M.Pi (Ici 0) q := by
  rw [ret_phi]
  constructor
  · intro h y hy
    have := h hy
    simp only [mem_setOf_eq] at this ⊢
    exact le_of_mul_le_mul_left this hφ0
  · intro h y hy
    have := h hy
    simp only [mem_setOf_eq] at this ⊢
    exact mul_le_mul_of_nonneg_left this hφ0.le

theorem rsc_core (M : Model) (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1)
    (qI : ℝ) (hqI0 : 0 ≤ qI) (hqI : IsMaxOn M.Pi (Set.Ici 0) qI) :
    (IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) qI ∧
      ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ (φ * M.c)) (Set.Ici 0) q → q = qI) ∧
    φ * M.c ≤ M.c ∧
    M.retailerProfit φ (φ * M.c) qI = φ * M.Pi qI ∧
    M.supplierProfit φ (φ * M.c) qI = (1 - φ) * M.Pi qI := by
  refine ⟨⟨(ret_max_iff M φ hφ0 qI).2 hqI, fun q hq hm =>
    rs_uniq (Pi_sc M) q qI hq hqI0 ((ret_max_iff M φ hφ0 q).1 hm) hqI⟩, ?_, ?_, ?_⟩
  · have := M.c_pos; nlinarith
  · simp only [Model.retailerProfit, Model.Pi]; ring
  · simp only [Model.supplierProfit, Model.Pi]; ring

theorem het_core (c φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    ∃ w : ℝ, 0 ≤ w ∧ ∀ M : Model, M.c = c → ∀ qI : ℝ, 0 ≤ qI →
      IsMaxOn M.Pi (Set.Ici 0) qI →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qI ∧
        ∀ q : ℝ, 0 ≤ q → IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q → q = qI := by
  by_cases hc : 0 < c
  · refine ⟨φ * c, by positivity, ?_⟩
    intro M hM qI hqI0 hqI
    subst hM
    exact (rsc_core M φ hφ0 hφ1 qI hqI0 hqI).1
  · refine ⟨0, le_rfl, ?_⟩
    intro M hM
    exact absurd (hM ▸ M.c_pos) hc

end RevShareCoord.Single

open RevShareCoord.Single


theorem solution (M : Model) (φ w : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w)
    (hR0 : w / φ < M.R' 0) :
    (∀ qhat : ℝ, 0 ≤ qhat →
      (IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qhat ↔ 0 < qhat ∧ φ * M.R' qhat = w)) ∧
    (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₁ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₂ → q₁ = q₂) := by
  exact retailer_first_order_core M φ w hφ0 hφ1 hw hR0
