-- Prove2me | solution 1 for TalagrandConc.OnePoint.prop_2_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:58:58.085772+00:00
-- url     : https://prove2.me/submissions/8ce0ff47-6e4d-46da-8c99-48e58d097bfe

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal
open scoped ENNReal Classical

namespace TalagrandConc.OnePoint

/-! ### The exponential integrand -/

lemma expMul_eq (t : ℝ) (ht : 0 ≤ t) (z : ℝ≥0∞) :
    expMul t z = EReal.exp (((ENNReal.ofReal t * z : ℝ≥0∞)) : EReal) := by
  unfold expMul
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ht]

lemma expMul_mono (t : ℝ) (ht : 0 ≤ t) {z₁ z₂ : ℝ≥0∞} (h : z₁ ≤ z₂) :
    expMul t z₁ ≤ expMul t z₂ := by
  rw [expMul_eq t ht, expMul_eq t ht]
  apply EReal.exp_monotone
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact mul_le_mul' le_rfl h

lemma expMul_add_const (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : 0 ≤ c) (z : ℝ≥0∞) :
    expMul t (ENNReal.ofReal c + z) = ENNReal.ofReal (Real.exp (t * c)) * expMul t z := by
  rw [expMul_eq t ht, expMul_eq t ht, mul_add, ← ENNReal.ofReal_mul ht, EReal.coe_ennreal_add,
    EReal.exp_add, EReal.coe_ennreal_ofReal, max_eq_left (by positivity), EReal.exp_coe]

lemma expMul_zero' (t : ℝ) : expMul t 0 = 1 := by
  unfold expMul
  simp

/-! ### Product integrals without measurability -/

lemma lintegral_prod_le_iter {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (h : X × Y → ℝ≥0∞) :
    ∫⁻ p, h p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, h (x, y) ∂ν ∂μ := by
  rw [lintegral_def]
  refine iSup₂_le fun φ hφ => ?_
  calc φ.lintegral (μ.prod ν) = ∫⁻ p, φ p ∂(μ.prod ν) := (φ.lintegral_eq_lintegral _).symm
    _ = ∫⁻ x, ∫⁻ y, φ (x, y) ∂ν ∂μ := lintegral_prod _ φ.measurable.aemeasurable
    _ ≤ ∫⁻ x, ∫⁻ y, h (x, y) ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hφ (x, y)

/-! ### Weighted Hamming distance and sections -/

/-- Prepending a coordinate. -/
def cns {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.cons (α := fun _ => Ω) ω z

@[simp] lemma cns_zero {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) : cns ω z 0 = ω := by
  simp [cns]

@[simp] lemma cns_succ {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) (j : Fin N) :
    cns ω z j.succ = z j := by
  simp [cns]

lemma wsum_cons {Ω : Type*} {N : ℕ} (a : Fin (N + 1) → ℝ) (ω ω' : Ω) (z z' : Fin N → Ω) :
    ∑ i ∈ Finset.univ.filter (fun i => cns ω z i ≠ cns ω' z' i), ENNReal.ofReal (a i)
      = (if ω ≠ ω' then ENNReal.ofReal (a 0) else 0)
        + ∑ j ∈ Finset.univ.filter (fun j => z j ≠ z' j), ENNReal.ofReal (a j.succ) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

lemma wd_le_of_mem {Ω : Type*} {N : ℕ} (a : Fin N → ℝ) (A : Set (Fin N → Ω))
    (x y : Fin N → Ω) (hy : y ∈ A) :
    weightedHammingDistToSet a A x
      ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ENNReal.ofReal (a i) := by
  unfold weightedHammingDistToSet
  exact iInf₂_le y hy

lemma le_wd {Ω : Type*} {N : ℕ} (a : Fin N → ℝ) (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    (c : ℝ≥0∞)
    (h : ∀ y ∈ A, c ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ENNReal.ofReal (a i)) :
    c ≤ weightedHammingDistToSet a A x := by
  unfold weightedHammingDistToSet
  exact le_iInf₂ h

/-- Section of a set along the first coordinate. -/
def sec {Ω : Type*} {N : ℕ} (ω : Ω) (A : Set (Fin (N + 1) → Ω)) : Set (Fin N → Ω) :=
  {z | cns ω z ∈ A}

lemma wd_cons_same {Ω : Type*} {N : ℕ} (a : Fin (N + 1) → ℝ) (A : Set (Fin (N + 1) → Ω))
    (ω : Ω) (z : Fin N → Ω) :
    weightedHammingDistToSet a A (cns ω z)
      ≤ weightedHammingDistToSet (fun j => a j.succ) (sec ω A) z := by
  apply le_wd
  intro y hy
  calc weightedHammingDistToSet a A (cns ω z)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => cns ω z i ≠ cns ω y i),
          ENNReal.ofReal (a i) := wd_le_of_mem a A _ _ hy
    _ = _ := by rw [wsum_cons]; simp

lemma wd_cons_other {Ω : Type*} {N : ℕ} (a : Fin (N + 1) → ℝ) (A : Set (Fin (N + 1) → Ω))
    (ω ω' : Ω) (z : Fin N → Ω) :
    weightedHammingDistToSet a A (cns ω z)
      ≤ ENNReal.ofReal (a 0) + weightedHammingDistToSet (fun j => a j.succ) (sec ω' A) z := by
  show _ ≤ ENNReal.ofReal (a 0) + ⨅ y ∈ sec ω' A, _
  rw [ENNReal.add_iInf]
  refine le_iInf fun y => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hy => ?_
  calc weightedHammingDistToSet a A (cns ω z)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => cns ω z i ≠ cns ω' y i),
          ENNReal.ofReal (a i) := wd_le_of_mem a A _ _ hy
    _ ≤ _ := by
        rw [wsum_cons]
        apply add_le_add _ le_rfl
        split_ifs <;> simp

/-! ### The scaled one-step inequality -/

lemma step_scaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (α : ℝ) (hα : 0 < α)
    (E K : ℝ≥0∞)
    (hstep : ∀ g : Ω → ℝ≥0∞, Measurable g → (∀ ω, g ω ≤ 1) →
      (∫⁻ ω, min E ((g ω) ^ (-α)) ∂μ) * (∫⁻ ω, g ω ∂μ) ^ α ≤ K)
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (D : ℝ≥0∞) (hD0 : D ≠ 0) (hDt : D ≠ ⊤)
    (hgD : ∀ ω, (g ω) ^ α ≤ D) :
    (∫⁻ ω, min E (D / (g ω) ^ α) ∂μ) * (∫⁻ ω, g ω ∂μ) ^ α ≤ K * D := by
  set s : ℝ≥0∞ := D ^ (-α⁻¹) with hs
  have hsα : s ^ α = D⁻¹ := by
    rw [hs, ← ENNReal.rpow_mul, neg_mul, inv_mul_cancel₀ hα.ne', ENNReal.rpow_neg_one]
  have hpow : ∀ x : ℝ≥0∞, (x * s) ^ α = x ^ α / D := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le, hsα, div_eq_mul_inv]
  set g' : Ω → ℝ≥0∞ := fun ω => g ω * s with hg'
  have hg'm : Measurable g' := hg.mul_const _
  have hg'1 : ∀ ω, g' ω ≤ 1 := by
    intro ω
    rw [← ENNReal.rpow_le_rpow_iff hα, ENNReal.one_rpow, hg', hpow, ENNReal.div_le_iff hD0 hDt,
      one_mul]
    exact hgD ω
  have h := hstep g' hg'm hg'1
  have hmin : ∀ ω, min E ((g' ω) ^ (-α)) = min E (D / (g ω) ^ α) := by
    intro ω
    rw [ENNReal.rpow_neg, hg', hpow, ENNReal.inv_div (Or.inl hDt) (Or.inl hD0)]
  simp_rw [hmin] at h
  rw [hg', lintegral_mul_const _ hg, hpow, ← mul_div_assoc, ENNReal.div_le_iff hD0 hDt] at h
  exact h

/-! ### The main induction -/

theorem main_induction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (N : ℕ) (a : Fin N → ℝ) (_ha : ∀ i, 0 ≤ a i) (K : Fin N → ℝ≥0∞)
      (_hK0 : ∀ i, K i ≠ 0) (_hKt : ∀ i, K i ≠ ⊤)
      (_hstep : ∀ i, ∀ g : Ω → ℝ≥0∞, Measurable g → (∀ ω, g ω ≤ 1) →
        (∫⁻ ω, min (ENNReal.ofReal (Real.exp (t * a i))) ((g ω) ^ (-α)) ∂μ) *
          (∫⁻ ω, g ω ∂μ) ^ α ≤ K i)
      (A : Set (Fin N → Ω)) (_hA : MeasurableSet A),
      (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ (∏ i, K i) / ((Measure.pi fun _ : Fin N => μ) A) ^ α := by
  intro N
  induction N with
  | zero =>
    intro a _ K hK0 _ _ A _
    rcases Set.eq_empty_or_nonempty A with hA | ⟨y, hy⟩
    · subst hA
      rw [measure_empty, ENNReal.zero_rpow_of_pos hα,
        ENNReal.div_zero (Finset.prod_ne_zero_iff.2 fun i _ => hK0 i)]
      exact le_top
    · have hS : (∫⁻ x, expMul t (weightedHammingDistToSet a A x)
          ∂(Measure.pi fun _ : Fin 0 => μ)) ≤ 1 := by
        have hd : ∀ x, weightedHammingDistToSet a A x = 0 := by
          intro x
          apply le_antisymm _ bot_le
          have := wd_le_of_mem a A x y hy
          simpa using this
        simp_rw [hd, expMul_zero']
        rw [lintegral_const, measure_univ, mul_one]
      have hR : 1 ≤ (∏ i : Fin 0, K i) / ((Measure.pi fun _ : Fin 0 => μ) A) ^ α := by
        rw [Finset.univ_eq_empty, Finset.prod_empty,
          ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top), one_mul]
        calc ((Measure.pi fun _ : Fin 0 => μ) A) ^ α ≤ (1 : ℝ≥0∞) ^ α :=
              ENNReal.rpow_le_rpow prob_le_one hα.le
          _ = 1 := ENNReal.one_rpow _
      exact hS.trans hR
  | succ N ih =>
    intro a ha K hK0 hKt hstep A hA
    set ν : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => μ with hν
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Ω) 0 with he
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (N + 1) => μ) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hsymm : ∀ p : Ω × (Fin N → Ω), e.symm p = cns p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      show Fin.insertNth (α := fun _ => Ω) 0 p.1 p.2 = _
      rw [Fin.insertNth_zero']
      rfl
    set S := e.symm ⁻¹' A with hS
    have hSm : MeasurableSet S := e.symm.measurable hA
    set g : Ω → ℝ≥0∞ := fun ω => ν (Prod.mk ω ⁻¹' S) with hg
    have hgm : Measurable g := measurable_measure_prodMk_left hSm
    have hg1 : ∀ ω, g ω ≤ 1 := fun ω => prob_le_one
    have hsec : ∀ ω, Prod.mk ω ⁻¹' S = sec ω A := by
      intro ω
      ext z
      simp [hS, sec, hsymm]
    have hgsec : ∀ ω, g ω = ν (sec ω A) := by
      intro ω
      simp only [hg]
      rw [hsec]
    have hsecm : ∀ ω, MeasurableSet (sec ω A) := by
      intro ω
      rw [← hsec]
      exact measurable_prodMk_left hSm
    have hPA : (Measure.pi fun _ : Fin (N + 1) => μ) A = ∫⁻ ω, g ω ∂μ := by
      rw [← mp.symm.measure_preimage_equiv A, Measure.prod_apply hSm]
    have hL : (∫⁻ x, expMul t (weightedHammingDistToSet a A x)
          ∂(Measure.pi fun _ : Fin (N + 1) => μ))
        = ∫⁻ p, expMul t (weightedHammingDistToSet a A (cns p.1 p.2)) ∂(μ.prod ν) := by
      rw [MeasurePreserving.lintegral_map_equiv _ e.symm mp.symm]
      simp_rw [hsymm]
    set a' : Fin N → ℝ := fun j => a j.succ with ha'
    set K' : Fin N → ℝ≥0∞ := fun j => K j.succ with hK'
    set Kp := ∏ j : Fin N, K' j with hKp
    have hKprod : ∏ i, K i = K 0 * Kp := by rw [hKp, Fin.prod_univ_succ]
    have ih' : ∀ B : Set (Fin N → Ω), MeasurableSet B →
        (∫⁻ z, expMul t (weightedHammingDistToSet a' B z) ∂ν) ≤ Kp / (ν B) ^ α :=
      fun B hB => ih a' (fun j => ha _) K' (fun j => hK0 _) (fun j => hKt _) (fun j => hstep _) B hB
    rcases eq_or_ne ((Measure.pi fun _ : Fin (N + 1) => μ) A) 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hα,
        ENNReal.div_zero (Finset.prod_ne_zero_iff.2 fun i _ => hK0 i)]
      exact le_top
    set G := ⨆ ω, (g ω) ^ α with hG
    have hgG : ∀ ω, (g ω) ^ α ≤ G := fun ω => le_iSup (fun ω => (g ω) ^ α) ω
    have hG1 : G ≤ 1 := iSup_le fun ω => by
      calc (g ω) ^ α ≤ (1 : ℝ≥0∞) ^ α := ENNReal.rpow_le_rpow (hg1 ω) hα.le
        _ = 1 := ENNReal.one_rpow _
    have hGt : G ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hG1
    have hG0 : G ≠ 0 := by
      intro hG0
      apply h0
      rw [hPA]
      have : ∀ ω, g ω = 0 := by
        intro ω
        have h1 := hgG ω
        rw [hG0] at h1
        have h2 : (g ω) ^ α = 0 := le_antisymm h1 bot_le
        rcases ENNReal.rpow_eq_zero_iff.1 h2 with h | h
        · exact h.1
        · exact absurd h.2 (by linarith)
      simp [this]
    set E := ENNReal.ofReal (Real.exp (t * a 0)) with hE
    have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
    have hKpt : Kp ≠ ⊤ := by
      rw [hKp]
      exact ENNReal.prod_ne_top fun j _ => hKt _
    have hinner : ∀ ω, (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
        ≤ Kp * min ((g ω) ^ α)⁻¹ (E * G⁻¹) := by
      intro ω
      have h1 : (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
          ≤ Kp * ((g ω) ^ α)⁻¹ := by
        calc (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
            ≤ ∫⁻ z, expMul t (weightedHammingDistToSet a' (sec ω A) z) ∂ν :=
              lintegral_mono fun z => expMul_mono t ht (wd_cons_same a A ω z)
          _ ≤ Kp / (ν (sec ω A)) ^ α := ih' _ (hsecm ω)
          _ = Kp * ((g ω) ^ α)⁻¹ := by rw [div_eq_mul_inv, hgsec]
      have h2 : ∀ ω', (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
          ≤ E * (Kp * ((g ω') ^ α)⁻¹) := by
        intro ω'
        calc (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
            ≤ ∫⁻ z, expMul t (ENNReal.ofReal (a 0)
                + weightedHammingDistToSet a' (sec ω' A) z) ∂ν :=
              lintegral_mono fun z => expMul_mono t ht (wd_cons_other a A ω ω' z)
          _ = ∫⁻ z, E * expMul t (weightedHammingDistToSet a' (sec ω' A) z) ∂ν := by
              simp_rw [expMul_add_const t ht (a 0) (ha 0)]
              rfl
          _ = E * ∫⁻ z, expMul t (weightedHammingDistToSet a' (sec ω' A) z) ∂ν :=
              lintegral_const_mul' _ _ hEt
          _ ≤ E * (Kp / (ν (sec ω' A)) ^ α) := mul_le_mul' le_rfl (ih' _ (hsecm ω'))
          _ = E * (Kp * ((g ω') ^ α)⁻¹) := by
              rw [div_eq_mul_inv, hgsec]
      have h2' : (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
          ≤ Kp * (E * G⁻¹) := by
        have hne : Nonempty Ω := Measure.nonempty_of_neZero μ
        calc (∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν)
            ≤ ⨅ ω', E * (Kp * ((g ω') ^ α)⁻¹) := le_iInf h2
          _ = Kp * (E * G⁻¹) := by
              rw [hG, ENNReal.inv_iSup]
              rcases eq_or_ne Kp 0 with hKp0 | hKp0
              · simp [hKp0]
              rcases eq_or_ne E 0 with hE0 | hE0
              · simp [hE0]
              rw [ENNReal.mul_iInf_of_ne hE0 hEt, ENNReal.mul_iInf_of_ne hKp0 hKpt]
              congr 1
              ext ω'
              ring
      have hmono : Monotone (fun x : ℝ≥0∞ => Kp * x) := fun _ _ h => mul_le_mul' le_rfl h
      rw [hmono.map_min]
      exact le_min h1 h2'
    have hmonoG : Monotone (fun x : ℝ≥0∞ => G⁻¹ * x) := fun _ _ h => mul_le_mul' le_rfl h
    have hmin : ∀ ω, min ((g ω) ^ α)⁻¹ (E * G⁻¹) = G⁻¹ * min E (G / (g ω) ^ α) := by
      intro ω
      rw [hmonoG.map_min, min_comm]
      congr 1
      · ring
      · rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hG0 hGt, one_mul]
    have hsg := step_scaled μ α hα E (K 0) (hstep 0) g hgm G hG0 hGt hgG
    set Y := ∫⁻ ω, min E (G / (g ω) ^ α) ∂μ with hY
    set u := ∫⁻ ω, g ω ∂μ with hu
    have hu0 : u ^ α ≠ 0 := by
      intro h
      rcases ENNReal.rpow_eq_zero_iff.1 h with h | h
      · exact h0 (hPA.trans h.1)
      · exact absurd h.2 (by linarith)
    have hu1 : u ≤ 1 := by
      rw [hu]
      calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg1
        _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
    have hut : u ^ α ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hα.le (ne_top_of_le_ne_top ENNReal.one_ne_top hu1)
    calc (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin (N + 1) => μ))
        = ∫⁻ p, expMul t (weightedHammingDistToSet a A (cns p.1 p.2)) ∂(μ.prod ν) := hL
      _ ≤ ∫⁻ ω, ∫⁻ z, expMul t (weightedHammingDistToSet a A (cns ω z)) ∂ν ∂μ :=
          lintegral_prod_le_iter μ ν _
      _ ≤ ∫⁻ ω, Kp * min ((g ω) ^ α)⁻¹ (E * G⁻¹) ∂μ := lintegral_mono hinner
      _ = Kp * ∫⁻ ω, min ((g ω) ^ α)⁻¹ (E * G⁻¹) ∂μ := lintegral_const_mul' _ _ hKpt
      _ = Kp * (G⁻¹ * Y) := by
          rw [hY]
          simp_rw [hmin]
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hG0)]
      _ ≤ (∏ i, K i) / ((Measure.pi fun _ : Fin (N + 1) => μ) A) ^ α := by
          rw [hKprod, hPA, ENNReal.le_div_iff_mul_le (Or.inl hu0) (Or.inl hut)]
          calc Kp * (G⁻¹ * Y) * u ^ α = (Kp * G⁻¹) * (Y * u ^ α) := by ring
            _ ≤ (Kp * G⁻¹) * (K 0 * G) := mul_le_mul' le_rfl hsg
            _ = K 0 * Kp * (G⁻¹ * G) := by ring
            _ = K 0 * Kp := by rw [ENNReal.inv_mul_cancel hG0 hGt, mul_one]


/-- Pointwise bound: `min(e^t, 1/g) + e^t g ≤ 1 + e^t` for `g ∈ [0,1]`. -/
lemma min_inv_add_le (t : ℝ) (g : ℝ≥0∞) (hg : g ≤ 1) :
    min (ENNReal.ofReal (Real.exp t)) g⁻¹ + ENNReal.ofReal (Real.exp t) * g
      ≤ 1 + ENNReal.ofReal (Real.exp t) := by
  set E := Real.exp t with hE
  have hE0 : 0 < E := Real.exp_pos t
  rcases eq_or_ne g 0 with h0 | h0
  · subst h0
    simp
  have hgt : g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hg
  set r := g.toReal with hr
  have hgr : g = ENNReal.ofReal r := (ENNReal.ofReal_toReal hgt).symm
  have hr0 : 0 < r := ENNReal.toReal_pos h0 hgt
  have hr1 : r ≤ 1 := by
    rw [hgr] at hg
    exact (ENNReal.ofReal_le_one).1 hg
  rw [hgr, ← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_mul hE0.le,
    show (1 : ℝ≥0∞) + ENNReal.ofReal E = ENNReal.ofReal (1 + E) by
      rw [ENNReal.ofReal_add zero_le_one hE0.le, ENNReal.ofReal_one]]
  rcases le_or_gt (E * r) 1 with h | h
  · calc min (ENNReal.ofReal E) (ENNReal.ofReal r⁻¹) + ENNReal.ofReal (E * r)
        ≤ ENNReal.ofReal E + ENNReal.ofReal (E * r) := add_le_add (min_le_left _ _) le_rfl
      _ = ENNReal.ofReal (E + E * r) := by rw [ENNReal.ofReal_add hE0.le (by positivity)]
      _ ≤ ENNReal.ofReal (1 + E) := ENNReal.ofReal_le_ofReal (by linarith)
  · calc min (ENNReal.ofReal E) (ENNReal.ofReal r⁻¹) + ENNReal.ofReal (E * r)
        ≤ ENNReal.ofReal r⁻¹ + ENNReal.ofReal (E * r) := add_le_add (min_le_right _ _) le_rfl
      _ = ENNReal.ofReal (r⁻¹ + E * r) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (1 + E) := by
          apply ENNReal.ofReal_le_ofReal
          have : r⁻¹ ≤ 1 + E - E * r := by
            rw [inv_eq_one_div, div_le_iff₀ hr0]
            nlinarith [mul_le_mul_of_nonneg_right h.le (sub_nonneg.2 hr1)]
          linarith

/-- The real quadratic bound `(1 + E - E u) u ≤ a(t)` with `E = e^t`. -/
lemma quad_le_aOne (t u : ℝ) :
    (1 + Real.exp t - Real.exp t * u) * u ≤ aOne t := by
  unfold aOne
  have hE0 : 0 < Real.exp t := Real.exp_pos t
  rw [Real.exp_neg]
  have key : aOne t - (1 + Real.exp t - Real.exp t * u) * u
      = (1 + Real.exp t - 2 * Real.exp t * u) ^ 2 / (4 * Real.exp t) := by
    unfold aOne
    rw [Real.exp_neg]
    field_simp
    ring
  have : 0 ≤ (1 + Real.exp t - 2 * Real.exp t * u) ^ 2 / (4 * Real.exp t) := by positivity
  unfold aOne at key
  rw [Real.exp_neg] at key
  linarith

/-- ENNReal-valued core of Lemma 2.1.2. -/
theorem lemma_2_1_2_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (g ω)⁻¹ ∂μ) * (∫⁻ ω, g ω ∂μ)
      ≤ ENNReal.ofReal (aOne t) := by
  set E := ENNReal.ofReal (Real.exp t) with hE
  set Y := ∫⁻ ω, min E (g ω)⁻¹ ∂μ with hY
  set u := ∫⁻ ω, g ω ∂μ with hu
  have hmeas : Measurable fun ω => min E (g ω)⁻¹ := measurable_const.min hg.inv
  have hsum : Y + E * u ≤ 1 + E := by
    rw [hY, hu, ← lintegral_const_mul E hg, ← lintegral_add_left hmeas]
    calc ∫⁻ ω, (min E (g ω)⁻¹ + E * g ω) ∂μ ≤ ∫⁻ _, (1 + E) ∂μ :=
          lintegral_mono fun ω => min_inv_add_le t (g ω) (hg1 ω)
      _ = 1 + E := by rw [lintegral_const, measure_univ, mul_one]
  have hu1 : u ≤ 1 := by
    rw [hu]
    calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg1
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hYt : Y ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hEt⟩) ?_
    exact le_trans le_self_add hsum
  have hut : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  set y := Y.toReal with hy
  set ur := u.toReal with hur
  have hY' : Y = ENNReal.ofReal y := (ENNReal.ofReal_toReal hYt).symm
  have hu' : u = ENNReal.ofReal ur := (ENNReal.ofReal_toReal hut).symm
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hur0 : 0 ≤ ur := ENNReal.toReal_nonneg
  have hur1 : ur ≤ 1 := by
    rw [hu'] at hu1
    exact ENNReal.ofReal_le_one.1 hu1
  have hE0 : 0 < Real.exp t := Real.exp_pos t
  have hsum' : y + Real.exp t * ur ≤ 1 + Real.exp t := by
    rw [hY', hu', hE, ← ENNReal.ofReal_mul hE0.le, ← ENNReal.ofReal_add hy0 (by positivity),
      show (1 : ℝ≥0∞) + ENNReal.ofReal (Real.exp t) = ENNReal.ofReal (1 + Real.exp t) by
        rw [ENNReal.ofReal_add zero_le_one hE0.le, ENNReal.ofReal_one]] at hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  rw [hY', hu', ← ENNReal.ofReal_mul hy0]
  apply ENNReal.ofReal_le_ofReal
  calc y * ur ≤ (1 + Real.exp t - Real.exp t * ur) * ur := by
        apply mul_le_mul_of_nonneg_right _ hur0
        linarith
    _ ≤ aOne t := quad_le_aOne t ur

theorem lemma_2_1_2_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (ENNReal.ofReal (g ω))⁻¹ ∂μ) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (aOne t) := by
  exact lemma_2_1_2_ennreal μ (fun ω => ENNReal.ofReal (g ω)) hg.ennreal_ofReal
    (fun ω => ENNReal.ofReal_le_one.2 (hg1 ω)) t


/-! ### Consequences: Proposition 2.1.1 and Remark 2.1.3 -/

lemma expMul_ofReal (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : 0 ≤ c) :
    expMul t (ENNReal.ofReal c) = ENNReal.ofReal (Real.exp (t * c)) := by
  have := expMul_add_const t ht c hc 0
  rwa [add_zero, expMul_zero', mul_one] at this

lemma expMul_measurable (t : ℝ) (ht : 0 ≤ t) : Measurable (expMul t) := by
  have hm : Monotone (expMul t) := fun _ _ h => expMul_mono t ht h
  exact hm.measurable

lemma hamming_eq_weighted {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) :
    hammingDistToSet A x = weightedHammingDistToSet (fun _ => (1 : ℝ)) A x := by
  unfold hammingDistToSet weightedHammingDistToSet
  refine iInf_congr fun y => iInf_congr fun _ => ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp

lemma aOne_ge_one (t : ℝ) : 1 ≤ aOne t := by
  unfold aOne
  have h1 : 0 < Real.exp t := Real.exp_pos t
  have h2 : 0 < Real.exp (-t) := Real.exp_pos _
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [sq_nonneg (Real.exp t - Real.exp (-t))]

lemma aOne_le_exp (t : ℝ) : aOne t ≤ Real.exp (t ^ 2 / 4) := by
  have hc : aOne t = Real.cosh (t / 2) ^ 2 := by
    unfold aOne
    rw [Real.cosh_eq]
    have h1 : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [h1, h2]
    nlinarith [h3]
  have h4 : Real.cosh (t / 2) ≤ Real.exp ((t / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have h5 : 0 ≤ Real.cosh (t / 2) := (Real.cosh_pos _).le
  calc aOne t = Real.cosh (t / 2) ^ 2 := hc
    _ ≤ Real.exp ((t / 2) ^ 2 / 2) ^ 2 := by gcongr
    _ = Real.exp (t ^ 2 / 4) := by rw [sq, ← Real.exp_add]; ring_nf

/-- Generic tail bound from exponential moment bounds (Chebyshev + optimisation). -/
lemma tail_bound {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ≥0∞) (hf : Measurable f) (Z : ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ s : ℝ, 0 ≤ s →
      (∫⁻ x, expMul s (f x) ∂P) ≤ ENNReal.ofReal (Real.exp (s ^ 2 * C / 4)) / Z)
    (u : ℝ) (hu : 0 ≤ u) :
    P {x | ENNReal.ofReal u ≤ f x} ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / C)) / Z := by
  rcases eq_or_lt_of_le hC with hC0 | hC0
  · subst hC0
    have h := hint 0 le_rfl
    simp only [expMul, EReal.coe_zero, zero_mul, EReal.exp_zero, lintegral_const, measure_univ,
      mul_one] at h
    rw [div_zero, Real.exp_zero, ENNReal.ofReal_one]
    norm_num at h
    calc P _ ≤ 1 := prob_le_one
      _ ≤ 1 / Z := by
        rw [ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top), one_mul]
        exact h
  set s := 2 * u / C with hs
  have hs0 : 0 ≤ s := by positivity
  have hsub : {x | ENNReal.ofReal u ≤ f x}
      ⊆ {x | ENNReal.ofReal (Real.exp (s * u)) ≤ expMul s (f x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [← expMul_ofReal s hs0 u hu]
    exact expMul_mono s hs0 hx
  have hmarkov := mul_meas_ge_le_lintegral₀ ((expMul_measurable s hs0).comp hf).aemeasurable
    (ENNReal.ofReal (Real.exp (s * u))) (μ := P)
  have hE0 : ENNReal.ofReal (Real.exp (s * u)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hEt : ENNReal.ofReal (Real.exp (s * u)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc P {x | ENNReal.ofReal u ≤ f x}
      ≤ P {x | ENNReal.ofReal (Real.exp (s * u)) ≤ expMul s (f x)} := measure_mono hsub
    _ ≤ (ENNReal.ofReal (Real.exp (s ^ 2 * C / 4)) / Z) / ENNReal.ofReal (Real.exp (s * u)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hE0) (Or.inl hEt), mul_comm]
        exact hmarkov.trans (hint s hs0)
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / C)) / Z := by
        have hcomm : ∀ (p q : ℝ≥0∞), p / Z / q = p / q / Z := by
          intro p q; simp only [div_eq_mul_inv]; ring
        have harg : s ^ 2 * C / 4 - s * u = -u ^ 2 / C := by
          rw [hs]; field_simp; ring
        rw [hcomm, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub, harg]

theorem prop_2_1_1_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A ∧
      ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * N / 4)) / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ k : ℝ, 0 ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
          ≤ ENNReal.ofReal (Real.exp (-k ^ 2 / N)) / (Measure.pi fun _ : Fin N => μ) A) := by
  have h1 : ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A := by
    intro t ht
    have hK0 : ENNReal.ofReal (aOne t) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by linarith [aOne_ge_one t])).ne'
    have := main_induction μ 1 one_pos t ht N (fun _ => 1) (fun _ => zero_le_one)
      (fun _ => ENNReal.ofReal (aOne t)) (fun _ => hK0) (fun _ => ENNReal.ofReal_ne_top)
      (by
        intro i g hg hg1
        simp only [mul_one, ENNReal.rpow_neg_one, ENNReal.rpow_one]
        exact lemma_2_1_2_ennreal μ g hg hg1 t) A hA
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.rpow_one] at this
    simp_rw [hamming_eq_weighted]
    exact this
  have h2 : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * N / 4)) / (Measure.pi fun _ : Fin N => μ) A := by
    intro t ht
    apply ENNReal.div_le_div_right
    rw [← ENNReal.ofReal_pow (by linarith [aOne_ge_one t])]
    apply ENNReal.ofReal_le_ofReal
    calc aOne t ^ N ≤ Real.exp (t ^ 2 / 4) ^ N := by
          gcongr
          · linarith [aOne_ge_one t]
          · exact aOne_le_exp t
      _ = Real.exp (t ^ 2 * N / 4) := by rw [← Real.exp_nat_mul]; ring_nf
  refine ⟨fun t ht => ⟨h1 t ht.le, h2 t ht.le⟩, ?_⟩
  intro k hk
  exact tail_bound (Measure.pi fun _ : Fin N => μ) (hammingDistToSet A) hf
    ((Measure.pi fun _ : Fin N => μ) A) N (Nat.cast_nonneg N)
    (fun s hs => (h1 s hs).trans (h2 s hs)) k hk

theorem remark_2_1_3_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (weightedHammingDistToSet a A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 4))
              / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ u : ℝ, 0 ≤ u →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ weightedHammingDistToSet a A x}
          ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / ∑ i, a i ^ 2))
              / (Measure.pi fun _ : Fin N => μ) A) := by
  have h1 : ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 4))
            / (Measure.pi fun _ : Fin N => μ) A := by
    intro t ht
    have hK0 : ∀ i, ENNReal.ofReal (aOne (t * a i)) ≠ 0 := fun i =>
      (ENNReal.ofReal_pos.2 (by linarith [aOne_ge_one (t * a i)])).ne'
    have := main_induction μ 1 one_pos t ht N a (fun i => (ha i).le)
      (fun i => ENNReal.ofReal (aOne (t * a i))) hK0 (fun _ => ENNReal.ofReal_ne_top)
      (by
        intro i g hg hg1
        simp only [ENNReal.rpow_neg_one, ENNReal.rpow_one]
        exact lemma_2_1_2_ennreal μ g hg hg1 (t * a i)) A hA
    rw [ENNReal.rpow_one] at this
    refine this.trans (ENNReal.div_le_div_right ?_ _)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [aOne_ge_one (t * a i)])]
    apply ENNReal.ofReal_le_ofReal
    calc ∏ i, aOne (t * a i) ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 4) :=
          Finset.prod_le_prod (fun i _ => by linarith [aOne_ge_one (t * a i)])
            (fun i _ => aOne_le_exp _)
      _ = Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 4) := by
          rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_div]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
  refine ⟨fun t ht => h1 t ht.le, ?_⟩
  intro u hu
  exact tail_bound (Measure.pi fun _ : Fin N => μ) (weightedHammingDistToSet a A) hf
    ((Measure.pi fun _ : Fin N => μ) A) (∑ i, a i ^ 2)
    (Finset.sum_nonneg fun i _ => sq_nonneg _) h1 u hu

end TalagrandConc.OnePoint

open TalagrandConc.OnePoint


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A ∧
      ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * N / 4)) / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ k : ℝ, 0 ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
          ≤ ENNReal.ofReal (Real.exp (-k ^ 2 / N)) / (Measure.pi fun _ : Fin N => μ) A) := by
  exact prop_2_1_1_core μ N A hA hf
