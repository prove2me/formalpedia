-- Prove2me | solution 1 for TalagrandConc.OnePoint.cor_2_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:09:26.740567+00:00
-- url     : https://prove2.me/submissions/3b0378bd-1f17-4e79-8c63-0559c73dfe53

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal
open scoped ENNReal NNReal Classical

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


/-! ### Hoeffding's scalar inequality -/

lemma hoeffding_scalar (u s : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 + u * (Real.exp s - 1) ≤ Real.exp (u * s + s ^ 2 / 8) := by
  set p : ℝ≥0 := ⟨u, hu0⟩ with hp
  have hpu : (p : ℝ) = u := rfl
  have hp1 : p ≤ 1 := by rw [← NNReal.coe_le_coe, hpu]; exact hu1
  set μ : Measure Bool := (PMF.bernoulli p hp1).toMeasure with hμ
  set X : Bool → ℝ := fun b => if b then (1 : ℝ) else 0 with hX
  have hXm : Measurable X := measurable_from_top
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 :=
    ae_of_all _ (fun b => by cases b <;> simp [hX])
  have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hXm.aemeasurable hb
  have hmean : ∫ x, X x ∂μ = u := by
    rw [hμ, PMF.integral_eq_sum]
    simp [PMF.bernoulli_apply, hX, hpu]
  have h := hsg.mgf_le s
  rw [hmean] at h
  unfold ProbabilityTheory.mgf at h
  rw [hμ, PMF.integral_eq_sum] at h
  simp [PMF.bernoulli_apply, hX, hpu, NNReal.coe_sub hp1] at h
  have e1 : Real.exp (-(s * u)) = Real.exp (-(u * s)) := by congr 1; ring
  have e2 : Real.exp (s * (1 - u)) = Real.exp s * Real.exp (-(u * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (u * s) * Real.exp (-(u * s)) = 1 := by rw [← Real.exp_add]; simp
  rw [e2, e1] at h
  have h' : Real.exp (-(u * s)) * (1 + u * (Real.exp s - 1)) ≤ Real.exp (s ^ 2 / 8) := by
    calc Real.exp (-(u * s)) * (1 + u * (Real.exp s - 1))
        = u * (Real.exp s * Real.exp (-(u * s))) + (1 - u) * Real.exp (-(u * s)) := by ring
      _ ≤ _ := h
      _ = Real.exp (s ^ 2 / 8) := by congr 1; ring
  calc 1 + u * (Real.exp s - 1)
      = Real.exp (u * s) * (Real.exp (-(u * s)) * (1 + u * (Real.exp s - 1))) := by
        rw [← mul_assoc, e3, one_mul]
    _ ≤ Real.exp (u * s) * Real.exp (s ^ 2 / 8) := by gcongr
    _ = Real.exp (u * s + s ^ 2 / 8) := by rw [Real.exp_add]

/-! ### The variational term and its bounds -/

/-- The term inside the supremum of (2.2.3). -/
noncomputable def termF (α t u : ℝ) : ℝ :=
  (1 + u * (Real.exp t - 1)) * (1 - u * (1 - Real.exp (-t / α))) ^ α

lemma base_nonneg (α t u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ 1 - u * (1 - Real.exp (-t / α)) := by
  have := Real.exp_pos (-t / α)
  nlinarith

lemma termF_le_exp (α t u : ℝ) (hα : 0 < α) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    termF α t u ≤ Real.exp (t ^ 2 / 8 * (1 + 1 / α)) := by
  unfold termF
  have h1 := hoeffding_scalar u t hu0 hu1
  have h2 := hoeffding_scalar u (-t / α) hu0 hu1
  have hb := base_nonneg α t u hu0 hu1
  have h2' : (1 - u * (1 - Real.exp (-t / α))) ^ α
      ≤ Real.exp (u * (-t / α) + (-t / α) ^ 2 / 8) ^ α := by
    apply Real.rpow_le_rpow hb _ hα.le
    rw [show 1 - u * (1 - Real.exp (-t / α)) = 1 + u * (Real.exp (-t / α) - 1) by ring]
    exact h2
  rw [← Real.exp_mul] at h2'
  calc (1 + u * (Real.exp t - 1)) * (1 - u * (1 - Real.exp (-t / α))) ^ α
      ≤ Real.exp (u * t + t ^ 2 / 8) * Real.exp ((u * (-t / α) + (-t / α) ^ 2 / 8) * α) :=
        mul_le_mul h1 h2' (Real.rpow_nonneg hb _) (Real.exp_pos _).le
    _ = Real.exp (t ^ 2 / 8 * (1 + 1 / α)) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring

/-- Chord bound: for `λ ∈ [0,1]`, `(1 - λ(1 - q))^(-α) ≤ 1 + λ(e^t - 1)` where `q = e^{-t/α}`. -/
lemma chord_bound (α t l : ℝ) (hα : 0 < α) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (1 - l * (1 - Real.exp (-t / α))) ^ (-α) ≤ 1 + l * (Real.exp t - 1) := by
  set q := Real.exp (-t / α) with hq
  have hq0 : 0 < q := Real.exp_pos _
  set r := 1 - l * (1 - q) with hr
  have hr0 : 0 < r := by
    have hr' : r = (1 - l) + l * q := by rw [hr]; ring
    rw [hr']
    rcases lt_or_eq_of_le hl1 with h | h
    · nlinarith [mul_nonneg hl0 hq0.le]
    · rw [h]; linarith
  -- weighted AM-GM: q^l ≤ (1 - l) * 1 + l * q = r
  have hamgm : (1 : ℝ) ^ (1 - l) * q ^ l ≤ (1 - l) * 1 + l * q :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) hl0 zero_le_one hq0.le (by ring)
  rw [Real.one_rpow, one_mul] at hamgm
  have hql : q ^ l = Real.exp (-t / α * l) := by rw [hq, Real.exp_mul]
  have h1 : Real.exp (-t / α * l) ≤ r := by rw [← hql, hr]; linarith
  -- raise to the power α
  have h2 : Real.exp (-t / α * l) ^ α ≤ r ^ α := Real.rpow_le_rpow (Real.exp_pos _).le h1 hα.le
  have h3 : Real.exp (-t / α * l) ^ α = Real.exp (-(t * l)) := by
    rw [← Real.exp_mul]; congr 1; field_simp
  rw [h3] at h2
  have h4 : r ^ (-α) ≤ Real.exp (t * l) := by
    rw [Real.rpow_neg hr0.le, show Real.exp (t * l) = (Real.exp (-(t * l)))⁻¹ by
      rw [Real.exp_neg, inv_inv]]
    exact inv_anti₀ (Real.exp_pos _) h2
  -- convexity of exp
  have h5 : Real.exp (t * l) ≤ 1 + l * (Real.exp t - 1) := by
    have hc := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (by linarith : (0 : ℝ) ≤ 1 - l)
      hl0 (by ring : (1 - l) + l = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    calc Real.exp (t * l) = Real.exp (l * t) := by ring_nf
      _ ≤ (1 - l) + l * Real.exp t := hc
      _ = 1 + l * (Real.exp t - 1) := by ring
  exact h4.trans h5

/-! ### The one-step inequality with exponent `α` -/

lemma step_alpha {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α t : ℝ) (hα : 0 < α) (ht : 0 ≤ t) (K : ℝ) (hK1 : 1 ≤ K)
    (hK : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → termF α t u ≤ K)
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ ω, g ω ≤ 1) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) ((g ω) ^ (-α)) ∂μ) * (∫⁻ ω, g ω ∂μ) ^ α
      ≤ ENNReal.ofReal K := by
  have hu1 : (∫⁻ ω, g ω ∂μ) ≤ 1 := by
    calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg1
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  have huα : (∫⁻ ω, g ω ∂μ) ^ α ≤ 1 := by
    calc (∫⁻ ω, g ω ∂μ) ^ α ≤ (1 : ℝ≥0∞) ^ α := ENNReal.rpow_le_rpow hu1 hα.le
      _ = 1 := ENNReal.one_rpow _
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · -- t = 0
    subst ht0
    rw [Real.exp_zero, ENNReal.ofReal_one]
    have hY : (∫⁻ ω, min (1 : ℝ≥0∞) ((g ω) ^ (-α)) ∂μ) ≤ 1 := by
      calc (∫⁻ ω, min (1 : ℝ≥0∞) ((g ω) ^ (-α)) ∂μ) ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ :=
            lintegral_mono fun ω => min_le_left _ _
        _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
    calc _ ≤ (1 : ℝ≥0∞) * 1 := mul_le_mul' hY huα
      _ = 1 := mul_one _
      _ ≤ ENNReal.ofReal K := ENNReal.one_le_ofReal.2 hK1
  -- t > 0
  set q := Real.exp (-t / α) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : 0 < t / α := div_pos ht0 hα
    rw [neg_div]
    linarith
  have h1q : (1 - q) ≠ 0 := by linarith
  have hqα : q ^ α = Real.exp (-t) := by
    rw [hq, ← Real.exp_mul]; congr 1; field_simp
  set E := Real.exp t with hE
  have hE1 : 1 < E := by rw [hE]; exact Real.one_lt_exp_iff.2 ht0
  set A := (E - q) / (1 - q) with hA
  set B := (E - 1) / (1 - q) with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) (by linarith)
  have hEA : E ≤ A := by
    rw [hA, le_div_iff₀ (by linarith)]
    nlinarith
  -- affine form of the chord
  have hAB : ∀ r : ℝ, A - B * r = 1 + (1 - r) / (1 - q) * (E - 1) := by
    intro r
    rw [hA, hB]
    field_simp
    ring
  -- real pointwise bound
  have hpt : ∀ r : ℝ, 0 < r → r ≤ 1 → min E (r ^ (-α)) ≤ A - B * r := by
    intro r hr0 hr1
    rcases le_or_gt r q with hrq | hrq
    · calc min E (r ^ (-α)) ≤ E := min_le_left _ _
        _ ≤ A - B * r := by
            rw [hA, hB]
            rw [show (E - q) / (1 - q) - (E - 1) / (1 - q) * r = (E - q - (E - 1) * r) / (1 - q) by
              ring]
            rw [le_div_iff₀ (by linarith)]
            nlinarith
    · set l := (1 - r) / (1 - q) with hl
      have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
      have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; linarith
      have hrl : r = 1 - l * (1 - q) := by rw [hl]; field_simp; ring
      calc min E (r ^ (-α)) ≤ r ^ (-α) := min_le_right _ _
        _ = (1 - l * (1 - Real.exp (-t / α))) ^ (-α) := by rw [← hrl]
        _ ≤ 1 + l * (Real.exp t - 1) := chord_bound α t l hα hl0 hl1
        _ = A - B * r := by rw [hAB r]
  -- ENNReal pointwise bound
  have hptE : ∀ ω, min (ENNReal.ofReal E) ((g ω) ^ (-α)) + ENNReal.ofReal B * g ω
      ≤ ENNReal.ofReal A := by
    intro ω
    rcases eq_or_ne (g ω) 0 with h0 | h0
    · rw [h0, mul_zero, add_zero]
      calc min (ENNReal.ofReal E) (0 ^ (-α)) ≤ ENNReal.ofReal E := min_le_left _ _
        _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hEA
    have hgt : g ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 ω)
    set r := (g ω).toReal with hr
    have hgr : g ω = ENNReal.ofReal r := (ENNReal.ofReal_toReal hgt).symm
    have hr0 : 0 < r := ENNReal.toReal_pos h0 hgt
    have hr1 : r ≤ 1 := by
      have := hg1 ω
      rw [hgr] at this
      exact ENNReal.ofReal_le_one.1 this
    rw [hgr, ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_min, ← ENNReal.ofReal_mul hB0,
      ← ENNReal.ofReal_add (le_min (by linarith) (Real.rpow_nonneg hr0.le _)) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hpt r hr0 hr1]
  -- integrate
  set Y := ∫⁻ ω, min (ENNReal.ofReal E) ((g ω) ^ (-α)) ∂μ with hY
  set u := ∫⁻ ω, g ω ∂μ with hu
  have hmeas : Measurable fun ω => min (ENNReal.ofReal E) ((g ω) ^ (-α)) :=
    measurable_const.min (hg.pow_const _)
  have hsum : Y + ENNReal.ofReal B * u ≤ ENNReal.ofReal A := by
    rw [hY, hu, ← lintegral_const_mul _ hg, ← lintegral_add_left hmeas]
    calc ∫⁻ ω, (min (ENNReal.ofReal E) ((g ω) ^ (-α)) + ENNReal.ofReal B * g ω) ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal A ∂μ := lintegral_mono hptE
      _ = ENNReal.ofReal A := by rw [lintegral_const, measure_univ, mul_one]
  have hYE : Y ≤ ENNReal.ofReal E := by
    rw [hY]
    calc ∫⁻ ω, min (ENNReal.ofReal E) ((g ω) ^ (-α)) ∂μ ≤ ∫⁻ _, ENNReal.ofReal E ∂μ :=
          lintegral_mono fun ω => min_le_left _ _
      _ = ENNReal.ofReal E := by rw [lintegral_const, measure_univ, mul_one]
  have hYt : Y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hYE
  have hut : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  set y := Y.toReal with hy
  set v := u.toReal with hv
  have hY' : Y = ENNReal.ofReal y := (ENNReal.ofReal_toReal hYt).symm
  have hu' : u = ENNReal.ofReal v := (ENNReal.ofReal_toReal hut).symm
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hv1 : v ≤ 1 := by
    rw [hu'] at hu1
    exact ENNReal.ofReal_le_one.1 hu1
  have hyE : y ≤ E := by
    rw [hY'] at hYE
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hYE
  have hsum' : y + B * v ≤ A := by
    rw [hY', hu', ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_add hy0 (by positivity)] at hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hsum
  rw [hY', hu', ENNReal.ofReal_rpow_of_nonneg hv0 hα.le, ← ENNReal.ofReal_mul hy0]
  apply ENNReal.ofReal_le_ofReal
  rcases le_or_gt v q with hvq | hvq
  · calc y * v ^ α ≤ E * q ^ α := by
          apply mul_le_mul hyE (Real.rpow_le_rpow hv0 hvq hα.le) (Real.rpow_nonneg hv0 _)
            (by linarith)
      _ = 1 := by rw [hqα, hE, ← Real.exp_add]; simp
      _ ≤ K := hK1
  · set l := (1 - v) / (1 - q) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
    have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; linarith
    have hvl : v = 1 - l * (1 - q) := by rw [hl]; field_simp; ring
    calc y * v ^ α ≤ (1 + l * (E - 1)) * v ^ α := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0 _)
          rw [← hAB v]
          linarith
      _ = termF α t l := by
          unfold termF
          rw [← hq, ← hE, ← hvl]
      _ ≤ K := hK l hl0 hl1

/-! ### Corollary 2.2.3 -/

theorem cor_2_2_3_part1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (N * (t ^ 2 / 8) * (1 + 1 / α)))
            / (Measure.pi fun _ : Fin N => μ) A ^ α := by
  set K := Real.exp (t ^ 2 / 8 * (1 + 1 / α)) with hK
  have hK1 : 1 ≤ K := Real.one_le_exp (by positivity)
  have hK0 : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have := main_induction μ α hα t ht N (fun _ => 1) (fun _ => zero_le_one)
    (fun _ => ENNReal.ofReal K) (fun _ => hK0) (fun _ => ENNReal.ofReal_ne_top)
    (by
      intro i g hg hg1
      simp only [mul_one]
      exact step_alpha μ α t hα ht K hK1 (fun u hu0 hu1 => termF_le_exp α t u hα hu0 hu1)
        g hg hg1) A hA
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  simp_rw [hamming_eq_weighted]
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [← ENNReal.ofReal_pow (by linarith), hK, ← Real.exp_nat_mul]
  congr 1
  ring

lemma mem_hamming_zero {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) (hx : x ∈ A) :
    hammingDistToSet A x = 0 := by
  apply le_antisymm _ bot_le
  unfold hammingDistToSet
  refine (iInf₂_le x hx).trans ?_
  simp

theorem cor_2_2_3_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (N * (t ^ 2 / 8) * (1 + 1 / α)))
            / (Measure.pi fun _ : Fin N => μ) A ^ α) ∧
    (0 < (Measure.pi fun _ : Fin N => μ) A → ∀ k : ℝ,
      Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal)) ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
        ≤ ENNReal.ofReal (Real.exp (-(2 / N) *
            (k - Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal))) ^ 2))) := by
  refine ⟨fun α hα t ht => cor_2_2_3_part1 μ N A hA α hα t ht, ?_⟩
  intro hpos k hk
  set P : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => μ with hP
  set p := (P A).toReal with hp
  have hPt : P A ≠ ⊤ := measure_ne_top _ _
  have hp0 : 0 < p := ENNReal.toReal_pos hpos.ne' hPt
  have hPp : P A = ENNReal.ofReal p := (ENNReal.ofReal_toReal hPt).symm
  have hp1 : p ≤ 1 := by
    have := prob_le_one (μ := P) (s := A)
    rw [hPp] at this
    exact ENNReal.ofReal_le_one.1 this
  set L := Real.log (1 / p) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hp0]; linarith)
  set σ := Real.sqrt (N / 2 * L) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσsq : σ ^ 2 = N / 2 * L := Real.sq_sqrt (by positivity)
  -- trivial cases
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, div_zero, neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  rcases eq_or_lt_of_le hk with hkσ | hkσ
  · rw [← hkσ]
    simp only [sub_self]
    norm_num
    exact prob_le_one
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le hL0 with hL0' | hLpos
  · -- L = 0: P A = 1, the set has measure zero
    have hp1' : p = 1 := by
      have h1 : 1 / p = 1 := by
        rcases Real.log_eq_zero.1 hL0'.symm with h | h | h
        · exact absurd h (by positivity)
        · exact h
        · linarith [one_div_pos.2 hp0]
      field_simp at h1
      linarith
    have hPA1 : P A = 1 := by rw [hPp, hp1', ENNReal.ofReal_one]
    have hσ0' : σ = 0 := by rw [hσ, ← hL0']; simp
    have hkpos : 0 < k := by rw [hσ0'] at hkσ; exact hkσ
    have hsub : {x | ENNReal.ofReal k ≤ hammingDistToSet A x} ⊆ Aᶜ := by
      intro x hx hxA
      simp only [Set.mem_ofPred_eq] at hx
      rw [mem_hamming_zero A x hxA] at hx
      have : ENNReal.ofReal k = 0 := le_antisymm hx bot_le
      rw [ENNReal.ofReal_eq_zero] at this
      linarith
    calc P {x | ENNReal.ofReal k ≤ hammingDistToSet A x} ≤ P Aᶜ := measure_mono hsub
      _ = 0 := by rw [prob_compl_eq_one_sub hA, hPA1, tsub_self]
      _ ≤ _ := zero_le'
  -- main case: L > 0, N ≥ 1, k > σ
  have hσpos : 0 < σ := by
    rw [hσ, Real.sqrt_pos]
    positivity
  have hLσ : L = 2 * σ ^ 2 / N := by rw [hσsq]; field_simp
  set s := 4 * (k - σ) / N with hs
  have hs0 : 0 < s := by positivity
  set β := s * σ / (2 * L) with hβ
  have hβ0 : 0 < β := by positivity
  have h1 := cor_2_2_3_part1 μ N A hA β hβ0 s hs0.le
  rw [← hP] at h1
  -- Chebyshev
  have hsub : {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
      ⊆ {x | ENNReal.ofReal (Real.exp (s * k)) ≤ expMul s (hammingDistToSet A x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [← expMul_ofReal s hs0.le k (by linarith)]
    exact expMul_mono s hs0.le hx
  have hmarkov := mul_meas_ge_le_lintegral₀ ((expMul_measurable s hs0.le).comp hf).aemeasurable
    (ENNReal.ofReal (Real.exp (s * k))) (μ := P)
  have hE0 : ENNReal.ofReal (Real.exp (s * k)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hEt : ENNReal.ofReal (Real.exp (s * k)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPβ : P A ^ β = ENNReal.ofReal (Real.exp (-(L * β))) := by
    rw [hPp, ENNReal.ofReal_rpow_of_pos hp0, Real.rpow_def_of_pos hp0, hL, one_div, Real.log_inv]
    congr 2
    ring
  have hexp : N * (s ^ 2 / 8) * (1 + 1 / β) - (-(L * β)) - s * k = -(2 / N) * (k - σ) ^ 2 := by
    have hkσ' : k - σ ≠ 0 := by linarith
    rw [hβ, hs, hLσ]
    field_simp
    ring
  calc P {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
      ≤ P {x | ENNReal.ofReal (Real.exp (s * k)) ≤ expMul s (hammingDistToSet A x)} :=
        measure_mono hsub
    _ ≤ (ENNReal.ofReal (Real.exp (N * (s ^ 2 / 8) * (1 + 1 / β))) / P A ^ β)
          / ENNReal.ofReal (Real.exp (s * k)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hE0) (Or.inl hEt), mul_comm]
        exact hmarkov.trans h1
    _ = ENNReal.ofReal (Real.exp (-(2 / N) * (k - σ) ^ 2)) := by
        rw [hPβ, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _),
          ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub, ← Real.exp_sub, hexp]

end TalagrandConc.OnePoint

open TalagrandConc.OnePoint


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (N * (t ^ 2 / 8) * (1 + 1 / α)))
            / (Measure.pi fun _ : Fin N => μ) A ^ α) ∧
    (0 < (Measure.pi fun _ : Fin N => μ) A → ∀ k : ℝ,
      Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal)) ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
        ≤ ENNReal.ofReal (Real.exp (-(2 / N) *
            (k - Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal))) ^ 2))) := by
  exact cor_2_2_3_core μ N A hA hf
