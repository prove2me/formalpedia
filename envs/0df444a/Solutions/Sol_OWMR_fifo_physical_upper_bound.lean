-- Prove2me | solution 1 for OWMR.fifo_physical_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T06:42:39.928812+00:00
-- url     : https://prove2.me/submissions/dc9a5ff0-9c8d-40c5-a7cd-e717dc5a3ef1

import Theorems.Thm_OWMR_fifo_engine_invariants
import Theorems.Thm_OWMR_ss_poisson_upper
import Theorems.Thm_OWMR_fifo_prep_bound
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

section coord

variable {α : Type} [MeasurableSpace α] [Zero α]

private lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [MeasurableSpace α] in
private lemma padHist_insertNth_lt {M : ℕ} (i : Fin (M + 1)) (a b : α) (z : Fin M → α) (s : ℕ)
    (hs : s < i.val) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) s
      = padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z) s := by
  have hsM : s < M + 1 := lt_trans hs i.2
  have hsM' : s < M := lt_of_lt_of_le hs (Nat.lt_succ_iff.1 i.2)
  simp only [padHist, dif_pos hsM]
  have he : (⟨s, hsM⟩ : Fin (M + 1)) = i.succAbove ⟨s, hsM'⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp [Fin.lt_def, hs]
  rw [he, Fin.insertNth_apply_succAbove (α := fun _ => α),
    Fin.insertNth_apply_succAbove (α := fun _ => α)]

omit [MeasurableSpace α] in
private lemma padHist_insertNth_self {M : ℕ} (i : Fin (M + 1)) (a : α) (z : Fin M → α) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) i.val = a := by
  simp only [padHist, dif_pos i.2]
  exact Fin.insertNth_apply_same (α := fun _ => α) i a z

/-- The `t`-th demand is independent of anything depending on the demands before `t`. -/
private lemma lintegral_coord (μ : Measure α) [IsProbabilityMeasure μ]
    (N t : ℕ) (ht : t < N) (Φ : (ℕ → α) → α → ℝ≥0∞)
    (hΦ : Measurable fun p : (ℕ → α) × α => Φ p.1 p.2)
    (hdep : ∀ (d d' : ℕ → α) (a : α), (∀ s < t, d s = d' s) → Φ d a = Φ d' a) :
    ∫⁻ z, Φ (padHist N z) (padHist N z t) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ z, ∫⁻ a, Φ (padHist N z) a ∂μ ∂(Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hD : Measurable fun z : Fin (M + 1) → α => padHist (M + 1) z := measurable_padHist' _
  set i : Fin (M + 1) := ⟨t, ht⟩ with hi
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => α) i with he
  have hsymm : ∀ p : α × (Fin M → α), e.symm p = Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    fun p => rfl
  have key : ∀ F : (Fin (M + 1) → α) → ℝ≥0∞,
      ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (M + 1) => μ)
        = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin M => μ)) := by
    intro F
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hind : ∀ (a b : α) (z : Fin M → α) (c : α),
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c
        = Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z)) c := by
    intro a b z c
    exact hdep _ _ c fun s hs => padHist_insertNth_lt i a b z s (by simpa [hi] using hs)
  have hins : Measurable fun p : α × (Fin M → α) => Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    e.symm.measurable
  have hG : Measurable fun p : α × (Fin M → α) =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2)) p.1 :=
    hΦ.comp ((hD.comp hins).prodMk measurable_fst)
  rw [key, key]
  simp only [hsymm]
  have hl : ∀ p : α × (Fin M → α),
      padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2) t = p.1 :=
    fun p => padHist_insertNth_self i p.1 p.2
  simp only [hl]
  rw [lintegral_prod_symm _ hG.aemeasurable]
  have hc : ∀ (a : α) (z : Fin M → α),
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c ∂μ
        = ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ := fun a z =>
    lintegral_congr fun c => hind a c z c
  simp only [hc]
  have hH : Measurable fun z : Fin M → α =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin M → α) × α =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.2 p.1)) p.2)
      (hΦ.comp ((hD.comp (hins.comp (measurable_snd.prodMk measurable_fst))).prodMk measurable_snd))
  have hprod := lintegral_prod (μ := μ) (ν := Measure.pi fun _ : Fin M => μ)
    (fun p : α × (Fin M → α) =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c p.2)) c ∂μ)
    (hH.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]

end coord

/-- Splitting off the first demand: `ρ^{⊗(T+1)} ≅ ρ ⊗ ρ^{⊗T}`. -/
private lemma lintegral_pi_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (T : ℕ)
    {F : ℝ≥0 × (Fin T → ℝ≥0) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => ρ) ∂ρ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => ρ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

private lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

private lemma lintegral_law_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = F 0 := by
  rw [lintegral_map hF (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

private lemma lintegral_law_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, F ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hF (measurable_psum _)]
  have hG : Measurable fun q : ℝ≥0 × (Fin n → ℝ≥0) => F ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)) :=
    hF.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, F (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, F (((z 0 : ℝ≥0) : ℝ) + ∑ j, ((Fin.tail z j : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, Fin.tail]
  rw [key, lintegral_pi_succ ρ n hG]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => F ((y : ℝ) + x)) (hF.comp (measurable_const_add _))
    (measurable_psum n)]


/-! ### Newsvendor costs `y ↦ 𝔼[H (y - X)⁺ + p (X - y)⁺]` -/

private noncomputable def nvCost {β : Type} [MeasurableSpace β] (P : Measure β) (X : β → ℝ)
    (H p y : ℝ) : ℝ :=
  ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0) ∂P

section nv

variable {β : Type} [MeasurableSpace β] (P : Measure β) [IsProbabilityMeasure P] (X : β → ℝ)

private lemma nv_integrable (hX : Integrable X P) (H p y : ℝ) :
    Integrable (fun b => H * max (y - X b) 0 + p * max (X b - y) 0) P :=
  (((integrable_const y).sub hX).pos_part.const_mul _).add
    ((hX.sub (integrable_const y)).pos_part.const_mul _)

omit [IsProbabilityMeasure P] in
private lemma nv_nonneg (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) : 0 ≤ nvCost P X H p y :=
  integral_nonneg fun b =>
    add_nonneg (mul_nonneg hH (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

private lemma nv_lower (hX : Integrable X P) (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    H * (y - ∫ b, X b ∂P) ≤ nvCost P X H p y ∧ p * (∫ b, X b ∂P - y) ≤ nvCost P X H p y := by
  have hi := nv_integrable P X hX H p y
  constructor
  · have e : H * (y - ∫ b, X b ∂P) = ∫ b, H * (y - X b) ∂P := by
      rw [integral_const_mul, integral_sub (integrable_const y) hX, integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((((integrable_const y).sub hX)).const_mul H) hi fun b => ?_
    have h1 : H * (y - X b) ≤ H * max (y - X b) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hH
    have h2 : 0 ≤ p * max (X b - y) 0 := mul_nonneg hp (le_max_right _ _)
    simp only
    linarith
  · have e : p * (∫ b, X b ∂P - y) = ∫ b, p * (X b - y) ∂P := by
      rw [integral_const_mul, integral_sub hX (integrable_const y), integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((hX.sub (integrable_const y)).const_mul p) hi fun b => ?_
    have h1 : p * (X b - y) ≤ p * max (X b - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp
    have h2 : 0 ≤ H * max (y - X b) 0 := mul_nonneg hH (le_max_right _ _)
    simp only
    linarith

private lemma nv_lip (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (y y' : ℝ) :
    |nvCost P X H p y - nvCost P X H p y'| ≤ (H + p) * |y - y'| := by
  unfold nvCost
  rw [← integral_sub (nv_integrable P X hX H p y) (nv_integrable P X hX H p y')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ b, |H * max (y - X b) 0 + p * max (X b - y) 0
          - (H * max (y' - X b) 0 + p * max (X b - y') 0)| ∂P
      ≤ ∫ _b, (H + p) * |y - y'| ∂P := by
        refine integral_mono ((nv_integrable P X hX H p y).sub
          (nv_integrable P X hX H p y')).abs (integrable_const _) fun b => ?_
        have k1 := abs_max_sub_max_le_abs (y - X b) (y' - X b) 0
        have k2 := abs_max_sub_max_le_abs (X b - y) (X b - y') 0
        rw [show y - X b - (y' - X b) = y - y' by ring] at k1
        rw [show X b - y - (X b - y') = -(y - y') by ring, abs_neg] at k2
        calc |H * max (y - X b) 0 + p * max (X b - y) 0
              - (H * max (y' - X b) 0 + p * max (X b - y') 0)|
            = |H * (max (y - X b) 0 - max (y' - X b) 0)
                + p * (max (X b - y) 0 - max (X b - y') 0)| := by ring_nf
          _ ≤ |H * (max (y - X b) 0 - max (y' - X b) 0)|
                + |p * (max (X b - y) 0 - max (X b - y') 0)| := abs_add_le _ _
          _ = H * |max (y - X b) 0 - max (y' - X b) 0|
                + p * |max (X b - y) 0 - max (X b - y') 0| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
          _ ≤ H * |y - y'| + p * |y - y'| :=
              add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
          _ = (H + p) * |y - y'| := by ring
    _ = (H + p) * |y - y'| := by simp [integral_const, probReal_univ]

private lemma nv_continuous (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    Continuous (nvCost P X H p) := by
  have hL : LipschitzWith (Real.toNNReal (H + p)) (nvCost P X H p) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    exact nv_lip P X hX H p hH hp y y'
  exact hL.continuous

end nv

private lemma whLoss_add (h p a b : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p (a + b) ≤ whLoss h p a + whLoss h p b := by
  unfold whLoss
  have k1 : max (a + b) 0 ≤ max a 0 + max b 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have k2 : max (-(a + b)) 0 ≤ max (-a) 0 + max (-b) 0 :=
    max_le (by linarith [le_max_left (-a) 0, le_max_left (-b) 0])
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left k1 hh
  have := mul_le_mul_of_nonneg_left k2 hp
  linarith

private lemma whLoss_sum {ι : Type} (s : Finset ι) (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (a : ι → ℝ) : whLoss h p (∑ i ∈ s, a i) ≤ ∑ i ∈ s, whLoss h p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [whLoss]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (whLoss_add h p _ _ hh hp).trans (add_le_add le_rfl ih)

private lemma whLoss_nonneg (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : 0 ≤ whLoss h p y := by
  unfold whLoss
  exact add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

/-! ### Integrability of lead-time demands -/

private lemma integrable_marginal {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

private lemma integrable_aggregate {n : ℕ} (N : Network n) (hN : N.Standing) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) N.aggregate := by
  unfold Network.aggregate
  have hm : Measurable fun x : DemandVec n => ∑ i, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
  have h : Integrable (fun x : DemandVec n => ∑ i, ((x i : ℝ≥0) : ℝ)) N.μ :=
    integrable_finsetSum _ fun i _ => by
      have h1 := integrable_toReal_of_lintegral_ne_top
        (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
        ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
      simpa using h1
  simpa [Function.comp_def, NNReal.coe_sum] using h

private lemma integrable_psum (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ)) (Measure.pi fun _ : Fin L => ρ) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => ρ) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 hρ

/-- If `v → 0`, then `limsup (u + v) ≤ limsup u` in `ℝ≥0∞`. -/
private lemma limsup_add_tendsto_zero (u v : ℕ → ℝ≥0∞) (hv : Tendsto v atTop (𝓝 0)) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, u n + v n ≤ u n + ε :=
    (hv.eventually (ge_mem_nhds hε')).mono fun n hn => add_le_add le_rfl hn
  calc limsup (fun n => u n + v n) atTop ≤ limsup (fun n => u n + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup hev
    _ = limsup u atTop + ε :=
        limsup_add_const atTop u _ (by isBoundedDefault) (by isBoundedDefault)


/-! ### Blocks of later demands -/

section block

variable {α : Type} [MeasurableSpace α] [Zero α]

/-- The sum of the `m` demands of periods `t, …, t+m-1` is independent of everything observed
before period `t`. -/
private lemma lintegral_block (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ≥0) (hg : Measurable g) (TT t : ℕ) :
    ∀ (m : ℕ), t + m ≤ TT → ∀ (X : (ℕ → α) → ℝ), Measurable X →
      (∀ (d d' : ℕ → α), (∀ s < t, d s = d' s) → X d = X d') →
      ∀ (G0 : ℝ → ℝ≥0∞), Measurable G0 →
      ∫⁻ z, G0 (X (padHist TT z) - ∑ j ∈ Finset.range m, (g (padHist TT z (t + j)) : ℝ))
          ∂(Measure.pi fun _ : Fin TT => μ)
        = ∫⁻ z, ∫⁻ y, G0 (X (padHist TT z) - y)
            ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ))
          ∂(Measure.pi fun _ : Fin TT => μ) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  intro m
  induction m with
  | zero =>
    intro _ X _ _ G0 hG0
    refine lintegral_congr fun z => ?_
    rw [lintegral_law_zero (μ.map g) (F := fun y => G0 (X (padHist TT z) - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    simp
  | succ m ih =>
    intro htm X hX hXdep G0 hG0
    have hgs : ∀ j, Measurable fun d : ℕ → α => (g (d (t + j)) : ℝ) := fun j =>
      (hg.comp (measurable_pi_apply (t + j))).coe_nnreal_real
    have hS : Measurable fun d : ℕ → α => ∑ j ∈ Finset.range m, (g (d (t + j)) : ℝ) :=
      Finset.measurable_sum _ fun j _ => hgs j
    set Φ : (ℕ → α) → α → ℝ≥0∞ := fun d a =>
      G0 (X d - ∑ j ∈ Finset.range m, (g (d (t + j)) : ℝ) - (g a : ℝ)) with hΦ
    have hΦm : Measurable fun q : (ℕ → α) × α => Φ q.1 q.2 :=
      hG0.comp (((hX.comp measurable_fst).sub (hS.comp measurable_fst)).sub
        (hg.comp measurable_snd).coe_nnreal_real)
    have hΦdep : ∀ (d d' : ℕ → α) (a : α), (∀ s < t + m, d s = d' s) → Φ d a = Φ d' a := by
      intro d d' a h
      simp only [hΦ]
      rw [hXdep d d' (fun s hs => h s (by omega))]
      congr 3
      exact Finset.sum_congr rfl fun j hj => by
        rw [h (t + j) (by have := Finset.mem_range.1 hj; omega)]
    have hstep := lintegral_coord μ TT (t + m) (by omega) Φ hΦm hΦdep
    have hL : ∀ z : Fin TT → α, G0 (X (padHist TT z)
        - ∑ j ∈ Finset.range (m + 1), (g (padHist TT z (t + j)) : ℝ))
        = Φ (padHist TT z) (padHist TT z (t + m)) := by
      intro z
      simp only [hΦ, Finset.sum_range_succ]
      congr 1
      ring
    simp_rw [hL]
    rw [hstep]
    set G1 : ℝ → ℝ≥0∞ := fun y => ∫⁻ a, G0 (y - (g a : ℝ)) ∂μ with hG1
    have hG1m : Measurable G1 :=
      Measurable.lintegral_prod_right' (f := fun q : ℝ × α => G0 (q.1 - (g q.2 : ℝ)))
        (hG0.comp (measurable_fst.sub (hg.comp measurable_snd).coe_nnreal_real))
    have hih := ih (by omega) X hX hXdep G1 hG1m
    have hrw : ∀ z : Fin TT → α, ∫⁻ a, Φ (padHist TT z) a ∂μ
        = G1 (X (padHist TT z) - ∑ j ∈ Finset.range m, (g (padHist TT z (t + j)) : ℝ)) :=
      fun z => rfl
    simp_rw [hrw]
    rw [hih]
    refine lintegral_congr fun z => ?_
    set x0 := X (padHist TT z)
    rw [lintegral_law_succ (μ.map g) m (F := fun y => G0 (x0 - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    have hswap : ∫⁻ y, G1 (x0 - y)
        ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ))
        = ∫⁻ b, ∫⁻ y, G0 (x0 - y - (b : ℝ))
          ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ)) ∂(μ.map g) := by
      have hrw2 : ∀ y : ℝ, G1 (x0 - y) = ∫⁻ b, G0 (x0 - y - (b : ℝ)) ∂(μ.map g) := by
        intro y
        simp only [hG1]
        rw [lintegral_map (f := fun b : ℝ≥0 => G0 (x0 - y - (b : ℝ)))
          (hG0.comp (measurable_const.sub measurable_coe_nnreal_real)) hg]
      simp_rw [hrw2]
      exact lintegral_lintegral_swap ((hG0.comp ((measurable_const.sub measurable_fst).sub
        measurable_snd.coe_nnreal_real)).aemeasurable)
    rw [hswap]
    refine lintegral_congr fun b => lintegral_congr fun y => ?_
    congr 1
    ring

end block

/-- The sum shifted by a lead time. -/
private lemma shift_sum_le (G : ℕ → ℝ) (hG : ∀ t, 0 ≤ G t) (L T : ℕ) :
    ∑ t ∈ Finset.range T, G t
      ≤ ∑ t ∈ Finset.range L, G t + ∑ t ∈ Finset.range T, (if t + L < T then G (t + L) else 0) := by
  rcases le_or_gt T L with h | h
  · have h1 : ∑ t ∈ Finset.range T, G t ≤ ∑ t ∈ Finset.range L, G t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) fun t _ _ => hG t
    have h2 : 0 ≤ ∑ t ∈ Finset.range T, (if t + L < T then G (t + L) else 0) :=
      Finset.sum_nonneg fun t _ => by split_ifs; exacts [hG _, le_rfl]
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, T = L + m := ⟨T - L, by omega⟩
    have e3 : ∑ t ∈ Finset.range (L + m), (if t + L < L + m then G (t + L) else 0)
        = ∑ t ∈ Finset.range m, G (t + L) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ L + m by omega)]
      have h4 : ∑ t ∈ Finset.Ico m (L + m), (if t + L < L + m then G (t + L) else 0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have := (Finset.mem_Ico.1 ht).1
          rw [if_neg (by omega)]
      rw [h4, add_zero]
      exact Finset.sum_congr rfl fun t ht => by
        rw [if_pos (by have := Finset.mem_range.1 ht; omega)]
    rw [Finset.sum_range_add, e3]
    exact le_of_eq (by congr 1; exact Finset.sum_congr rfl fun k _ => by rw [add_comm])

/-! ### Network positions -/

/-- Retailer `i`'s position after the dispatches of period `t`: net inventory plus everything
dispatched to `i` and still in transit. -/
private noncomputable def retPos {n : ℕ} {U : Type} (N : Network n) (x : InitState n)
    (π : Policy n U) (i : Fin n) (t : ℕ) (ω : U × (ℕ → DemandVec n)) : ℝ :=
  (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s)
    + ∑ r ∈ Finset.range (t + 1), π.dispatch r ω.1 ω.2 i
    - ∑ r ∈ Finset.range t, ((ω.2 r i : ℝ≥0) : ℝ)

/-- The pooled position after the supplier order of period `t`, with each retailer centred by
`cZ i = 𝔼 Zᵢ`. -/
private noncomputable def poolPos {n : ℕ} {U : Type} (N : Network n) (x : InitState n)
    (π : Policy n U) (cZ : Fin n → ℝ) (t : ℕ) (ω : U × (ℕ → DemandVec n)) : ℝ :=
  (x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - cZ i))
    + ∑ r ∈ Finset.range (t + 1), π.order r ω.1 ω.2
    - ∑ r ∈ Finset.range t, ((∑ i, ω.2 r i : ℝ≥0) : ℝ)

private lemma netInv_shift {n : ℕ} {U : Type} (N : Network n) (x : InitState n)
    (π : Policy n U) (u : U) (d : ℕ → DemandVec n) (i : Fin n) (t : ℕ) :
    Policy.netInv N x π u d i (t + N.L i)
      = retPos N x π i t (u, d) - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ) := by
  unfold Policy.netInv retPos
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ s ∈ Finset.range (t + N.L i + 1), Policy.retArrival N x π u d i s
      = ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + ∑ r ∈ Finset.range (t + 1), π.dispatch r u d i := by
    rw [show t + N.L i + 1 = N.L i + (t + 1) by omega, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun s hs => by
        simp only [Policy.retArrival, if_pos (Finset.mem_range.1 hs)]
    · exact Finset.sum_congr rfl fun r _ => by
        simp only [Policy.retArrival, if_neg (show ¬(N.L i + r < N.L i) by omega),
          Nat.add_sub_cancel_left]
  have h2 : ∑ s ∈ Finset.range (t + N.L i + 1), ((d s i : ℝ≥0) : ℝ)
      = ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)
        + ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ) := by
    rw [show t + N.L i + 1 = t + (N.L i + 1) by omega, Finset.sum_range_add]
  rw [h1, h2]
  ring

private lemma pool_shift {n : ℕ} {U : Type} (N : Network n) (x : InitState n)
    (π : Policy n U) (cZ : Fin n → ℝ) (u : U) (d : ℕ → DemandVec n) (t : ℕ) :
    Policy.whStock N x π u d (t + N.L0) + ∑ i, (retPos N x π i (t + N.L0) (u, d) - cZ i)
      = poolPos N x π cZ t (u, d)
        - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) := by
  have h1 : ∑ s ∈ Finset.range (t + N.L0 + 1), Policy.supArrival N x π u d s
      = ∑ s ∈ Finset.range N.L0, x.supPipe s + ∑ r ∈ Finset.range (t + 1), π.order r u d := by
    rw [show t + N.L0 + 1 = N.L0 + (t + 1) by omega, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun s hs => by
        simp only [Policy.supArrival, if_pos (Finset.mem_range.1 hs)]
    · exact Finset.sum_congr rfl fun r _ => by
        simp only [Policy.supArrival, if_neg (show ¬(N.L0 + r < N.L0) by omega),
          Nat.add_sub_cancel_left]
  have h2 : ∑ i, ∑ r ∈ Finset.range (t + N.L0), ((d r i : ℝ≥0) : ℝ)
      = ∑ r ∈ Finset.range t, ((∑ i, d r i : ℝ≥0) : ℝ)
        + ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_range_add]
    simp only [NNReal.coe_sum]
  have h3 : ∑ i, ∑ r ∈ Finset.range (t + N.L0 + 1), π.dispatch r u d i
      = ∑ s ∈ Finset.range (t + N.L0 + 1), ∑ i, π.dispatch s u d i := Finset.sum_comm
  have hW : Policy.whStock N x π u d (t + N.L0)
      = x.W + ∑ s ∈ Finset.range (t + N.L0 + 1), Policy.supArrival N x π u d s
        - ∑ s ∈ Finset.range (t + N.L0 + 1), ∑ i, π.dispatch s u d i := by
    unfold Policy.whStock
    rw [Finset.sum_sub_distrib]
    ring
  have hR : ∑ i, (retPos N x π i (t + N.L0) (u, d) - cZ i)
      = ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - cZ i)
        + ∑ i, ∑ r ∈ Finset.range (t + N.L0 + 1), π.dispatch r u d i
        - ∑ i, ∑ r ∈ Finset.range (t + N.L0), ((d r i : ℝ≥0) : ℝ) := by
    unfold retPos
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hW, hR, h1, h3, h2]
  unfold poolPos
  ring

/-! ### The explicit processes driving `π_FIFO` -/

private lemma L_le_Tpipe {n : ℕ} (N : Network n) (i : Fin n) : N.L i ≤ N.Tpipe :=
  le_trans (Finset.le_sup (f := N.L) (Finset.mem_univ i)) (le_max_right _ _)

section proc

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

/-- The start condition (Appendix B, Step 1): all prescribed pipelines have arrived and every
retailer position is at most its target. -/
private def actE (d : ℕ → DemandVec n) (t : ℕ) : Prop :=
  N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i

private noncomputable instance actE_dec (d : ℕ → DemandVec n) : DecidablePred (actE N x c d) := fun t => by
  unfold actE; infer_instance

/-- The supplier echelon position before the order of period `t`. -/
private noncomputable def YpE (d : ℕ → DemandVec n) : ℕ → ℝ
  | 0 => x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
  | t + 1 => (if actE N x c d t ∧ YpE d t ≤ c.s0 then c.S0 else YpE d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ)

/-- Retailer request positions `P̂` after the requests of period `t`. -/
private noncomputable def PhE (d : ℕ → DemandVec n) : ℕ → Fin n → ℝ
  | 0 => fun i => if actE N x c d 0 then c.S i
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
  | t + 1 => fun i => if actE N x c d (t + 1) then
      (if actE N x c d t then (if PhE d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
        else PhE d t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ)

/-- Retailer request positions before the requests of period `t` (`Sᵢ` at the start). -/
private noncomputable def XrE (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  if t = 0 then c.S i else if actE N x c d (t - 1)
    then PhE N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) else c.S i

private lemma actE_mono (d : ℕ → DemandVec n) (t : ℕ) (h : actE N x c d t) :
    actE N x c d (t + 1) := by
  refine ⟨by have := h.1; omega, fun i => ?_⟩
  have := h.2 i
  rw [Finset.sum_range_succ]
  have : (0 : ℝ) ≤ ((d t i : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  linarith

private lemma actE_mono' (d : ℕ → DemandVec n) {r t : ℕ} (hrt : r ≤ t) (h : actE N x c d r) :
    actE N x c d t := by
  induction t with
  | zero => have : r = 0 := by omega
            subst this; exact h
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hrt) with h' | h'
    · exact actE_mono N x c d t (ih (by omega))
    · rw [← h']; exact h

private lemma actE_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    actE N x c d t ↔ actE N x c d' t := by
  unfold actE
  have e : ∀ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) = ∑ s ∈ Finset.range t, ((d' s i : ℝ≥0) : ℝ) :=
    fun i => Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]
  simp only [e]

private lemma meas_dsum (t : ℕ) (i : Fin n) :
    Measurable fun d : ℕ → DemandVec n => ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun s _ =>
    ((measurable_pi_apply i).comp (measurable_pi_apply s)).coe_nnreal_real

private lemma actE_meas (t : ℕ) : MeasurableSet {d : ℕ → DemandVec n | actE N x c d t} := by
  unfold actE
  have : {d : ℕ → DemandVec n | N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i}
      = {_d | N.Tpipe ≤ t + 1} ∩ ⋂ i, {d | x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i} := by
    ext d; simp
  rw [this]
  exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun i =>
    measurableSet_le (measurable_const.sub (meas_dsum t i)) measurable_const)

private lemma YpE_dep : ∀ (t : ℕ) (d d' : ℕ → DemandVec n), (∀ r < t, d r = d' r) →
    YpE N x c d t = YpE N x c d' t
  | 0, _, _, _ => rfl
  | t + 1, d, d', h => by
    simp only [YpE]
    rw [YpE_dep t d d' (fun r hr => h r (by omega)), h t (by omega)]
    by_cases ha : actE N x c d t
    · have ha' := (actE_dep N x c t d d' (fun r hr => h r (by omega))).1 ha
      simp only [ha, ha', true_and]
    · have ha' : ¬ actE N x c d' t := fun h' => ha ((actE_dep N x c t d d' (fun r hr => h r (by omega))).2 h')
      simp only [ha, ha', false_and, if_false]

private lemma YpE_meas : ∀ t, Measurable fun d : ℕ → DemandVec n => YpE N x c d t
  | 0 => measurable_const
  | t + 1 => by
    simp only [YpE]
    refine Measurable.sub (Measurable.ite ((actE_meas N x c t).inter
      (measurableSet_le (YpE_meas t) measurable_const)) measurable_const (YpE_meas t))
      (Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp (measurable_pi_apply t)).coe_nnreal_real)

private lemma PhE_dep : ∀ (t : ℕ) (d d' : ℕ → DemandVec n), (∀ r < t, d r = d' r) →
    ∀ i, PhE N x c d t i = PhE N x c d' t i
  | 0, d, d', h, i => by
    simp only [PhE]
    by_cases ha : actE N x c d 0
    · have ha' := (actE_dep N x c 0 d d' h).1 ha
      simp only [ha, ha', if_true]
    · have ha' : ¬ actE N x c d' 0 := fun h' => ha ((actE_dep N x c 0 d d' h).2 h')
      simp only [ha, ha', if_false]
  | t + 1, d, d', h, i => by
    simp only [PhE]
    have h1 := actE_dep N x c (t + 1) d d' h
    have h2 := actE_dep N x c t d d' (fun r hr => h r (by omega))
    rw [PhE_dep t d d' (fun r hr => h r (by omega)) i, h t (by omega)]
    have h3 : ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ)
        = ∑ s ∈ Finset.range (t + 1), ((d' s i : ℝ≥0) : ℝ) :=
      Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]
    rw [h3]
    by_cases ha : actE N x c d (t + 1)
    · by_cases hb : actE N x c d t
      · simp only [ha, h1.1 ha, hb, h2.1 hb, if_true]
      · have hb' : ¬ actE N x c d' t := fun h' => hb (h2.2 h')
        simp only [ha, h1.1 ha, hb, hb', if_true, if_false]
    · have ha' : ¬ actE N x c d' (t + 1) := fun h' => ha (h1.2 h')
      simp only [ha, ha', if_false]

private lemma PhE_meas : ∀ t i, Measurable fun d : ℕ → DemandVec n => PhE N x c d t i
  | 0, i => by
    simp only [PhE]
    exact Measurable.ite (actE_meas N x c 0) measurable_const measurable_const
  | t + 1, i => by
    simp only [PhE]
    have hd : Measurable fun d : ℕ → DemandVec n => ((d t i : ℝ≥0) : ℝ) :=
      ((measurable_pi_apply i).comp (measurable_pi_apply t)).coe_nnreal_real
    refine Measurable.ite (actE_meas N x c (t + 1)) (Measurable.ite (actE_meas N x c t)
      (Measurable.ite (measurableSet_le ((PhE_meas t i).sub hd) measurable_const) measurable_const
        ((PhE_meas t i).sub hd)) measurable_const) (measurable_const.sub (meas_dsum (t + 1) i))

private lemma XrE_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) (i : Fin n) :
    XrE N x c d t i = XrE N x c d' t i := by
  unfold XrE
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp [ht]
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right]
    have h1 := actE_dep N x c t' d d' (fun r hr => h r (by omega))
    rw [PhE_dep N x c t' d d' (fun r hr => h r (by omega)) i, h t' (by omega)]
    by_cases ha : actE N x c d t'
    · simp only [ha, h1.1 ha, if_true]
    · have ha' : ¬ actE N x c d' t' := fun h' => ha (h1.2 h')
      simp only [ha, ha', if_false]

private lemma XrE_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => XrE N x c d t i := by
  unfold XrE
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp only [ht, if_true]; exact measurable_const
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right]
    exact Measurable.ite (actE_meas N x c t') ((PhE_meas N x c t' i).sub
      ((measurable_pi_apply i).comp (measurable_pi_apply t')).coe_nnreal_real) measurable_const

/-- In preparation periods the supplier position just loses the demand. -/
private lemma YpE_prep (d : ℕ → DemandVec n) : ∀ t, ¬ actE N x c d t →
    YpE N x c d t = YpE N x c d 0 - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
  | 0, _ => by simp
  | t + 1, h => by
    have h' : ¬ actE N x c d t := fun h'' => h (actE_mono N x c d t h'')
    show (if actE N x c d t ∧ YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ) = _
    rw [if_neg (fun hh => h' hh.1), YpE_prep d t h', Finset.sum_range_succ]
    ring

private lemma PhE_prep (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ actE N x c d t) (i : Fin n) :
    PhE N x c d t i = x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) := by
  rcases t with _ | t
  · simp [PhE, h]
  · simp only [PhE, if_neg h]

/-- Once started, the request position is the `(sᵢ,Sᵢ)` post-action position. -/
private lemma PhE_post (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ)
    (h : actE N x c d t) (i : Fin n) :
    PhE N x c d t i = if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i := by
  unfold XrE
  rcases t with _ | t
  · simp only [PhE, h, if_true]
    split_ifs <;> rfl
  · simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right]
    by_cases ht : actE N x c d t
    · simp only [PhE, h, ht, if_true]
    · simp only [PhE, h, ht, if_true, if_false]
      split_ifs <;> rfl

private lemma XrE_step (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ)
    (h : actE N x c d t) (i : Fin n) :
    XrE N x c d (t + 1) i
      = (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i) - ((d t i : ℝ≥0) : ℝ) := by
  rw [← PhE_post N x c hsS d t h i]
  simp only [XrE, Nat.succ_ne_zero, if_false, add_tsub_cancel_right, if_pos h]

end proc

/-! ### Lemma 8 and the pathwise cost bound -/

/-- Lemma 8 (with an arbitrary subset of retailers): warehouse stock plus the retailers' costs,
evaluated at physical positions, are bounded by the echelon loss, the mirror losses and the costs
at request positions, since the stock and the unallocated quantities are never both positive. -/
private lemma lemma8_alg {n : ℕ} (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (H : Fin n → ℝ)
    (hH : ∀ i, 0 ≤ H i) (W : ℝ) (hW : 0 ≤ W) (Ph RP a Z : Fin n → ℝ) (hRP : ∀ i, RP i ≤ Ph i)
    (hWΔ : W * ∑ i, (Ph i - RP i) = 0) (A : Fin n → Prop) [DecidablePred A] :
    h * W + ∑ i, (if A i then H i * max (RP i - Z i) 0 + p * max (-(RP i - Z i)) 0 else 0)
      ≤ whLoss h p (W + ∑ i, (RP i - a i)) + ∑ i, whLoss h p (a i - Ph i)
        + ∑ i, (if A i then H i * max (Ph i - Z i) 0 + p * max (-(Ph i - Z i)) 0 else 0) := by
  set D := ∑ i, (Ph i - RP i) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => by linarith [hRP i]
  have h1 : ∀ i, (if A i then H i * max (RP i - Z i) 0 + p * max (-(RP i - Z i)) 0 else 0)
      ≤ (if A i then H i * max (Ph i - Z i) 0 + p * max (-(Ph i - Z i)) 0 else 0)
        + p * (Ph i - RP i) := by
    intro i
    have hd := hRP i
    split_ifs
    · have k1 : max (RP i - Z i) 0 ≤ max (Ph i - Z i) 0 := max_le_max (by linarith) le_rfl
      have k2 : max (-(RP i - Z i)) 0 ≤ max (-(Ph i - Z i)) 0 + (Ph i - RP i) :=
        max_le (by linarith [le_max_left (-(Ph i - Z i)) 0])
          (by linarith [le_max_right (-(Ph i - Z i)) 0])
      have := mul_le_mul_of_nonneg_left k1 (hH i)
      have := mul_le_mul_of_nonneg_left k2 hp
      nlinarith
    · nlinarith
  have h2 : h * W + p * D = whLoss h p (W - D) := by
    unfold whLoss
    rcases eq_or_lt_of_le hD0 with hz | hz
    · rw [← hz]
      simp only [mul_zero, add_zero, sub_zero, max_eq_left hW, max_eq_right (neg_nonpos.2 hW)]
    · have hW0 : W = 0 := by
        rcases mul_eq_zero.1 hWΔ with h' | h'
        · exact h'
        · exact absurd h' hz.ne'
      rw [hW0, zero_sub, mul_zero, zero_add, max_eq_right (by linarith), mul_zero, zero_add,
        neg_neg, max_eq_left hD0]
  have h3 : W - D = (W + ∑ i, (RP i - a i)) + ∑ i, (a i - Ph i) := by
    have e : ∑ i, (RP i - a i) + ∑ i, (a i - Ph i) = -D := by
      rw [← Finset.sum_add_distrib, hD, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have h4 := whLoss_add h p (W + ∑ i, (RP i - a i)) (∑ i, (a i - Ph i)) hh hp
  have h5 := whLoss_sum Finset.univ h p hh hp (fun i => a i - Ph i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [h3] at h2
  linarith

section path

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private noncomputable def cH (i : Fin n) (y : ℝ) : ℝ := N.H i * max y 0 + N.p * max (-y) 0

private noncomputable def YpostE (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  if actE N x c d t ∧ YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t

private lemma YpE_sum (d : ℕ → DemandVec n) : ∀ t, YpE N x c d t = YpE N x c d 0
    + ∑ r ∈ Finset.range t, (YpostE N x c d r - YpE N x c d r)
    - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
  | 0 => by simp
  | t + 1 => by
    have h1 := YpE_sum d t
    have h2 : YpE N x c d (t + 1) = YpostE N x c d t - ∑ i, ((d t i : ℝ≥0) : ℝ) := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- The real-valued pathwise bound. -/
private noncomputable def RB (d : ℕ → DemandVec n) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
      * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0)
  + N.Kmax * (n + N.L0)
  + ∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then N.K i
      * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0)
  + ∑ i, ∑ t ∈ Finset.range (N.L i),
      cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
  + ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
      - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
  + ∑ t ∈ Finset.range T, (if t + N.L0 < T then whLoss N.h N.p (YpostE N x c d t
      - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ)) else 0)
  + ∑ i, ∑ t ∈ Finset.range T, (if t + N.L i < T then cH N i (PhE N x c d t i
      - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
  + ∑ i, ∑ t ∈ Finset.range T, whLoss N.h N.p (c.a i - PhE N x c d t i)

private lemma path_bound (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i)
    (hs0 : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ t ∈ Finset.range T, Policy.periodCost N x (fifoPolicy N x c).toPolicy () d t
      ≤ RB N x c d T := by
  have hK0 := hN.K0_nonneg
  have hK := hN.K_nonneg
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hH : ∀ i, 0 ≤ N.H i := fun i => (hN.H_pos i).le
  obtain ⟨hO1, hO2, hO3, hO4, hO5⟩ := fifo_engine_invariants N hN x hx c hsS hs0 d (actE N x c d)
    (fun t => Iff.rfl) (YpE N x c d) rfl (fun t => rfl) (PhE N x c d) (fun i => rfl)
    (fun t i => rfl)
  set π := (fifoPolicy N x c).toPolicy with hπ
  have hord : ∀ t, π.order t () d = YpostE N x c d t - YpE N x c d t := fun t => by
    rw [hO1 t]; unfold YpostE; split_ifs <;> ring
  -- notation
  set W : ℕ → ℝ := fun t => Policy.whStock N x π () d t with hWdef
  set RP : ℕ → Fin n → ℝ := fun t i => retPos N x π i t ((), d) with hRPdef
  have hRPe : ∀ t i, RP t i = x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      + ∑ r ∈ Finset.range (t + 1), π.dispatch r () d i - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) :=
    fun t i => rfl
  -- the period cost, split
  have hpc : ∀ t, Policy.periodCost N x π () d t
      = (N.K0 * (if 0 < π.order t () d then 1 else 0)
        + ∑ i, N.K i * (if 0 < π.dispatch t () d i then 1 else 0))
        + (N.h * W t + ∑ i, cH N i (Policy.netInv N x π () d i t)) := fun t => by
    unfold Policy.periodCost cH; ring
  simp_rw [hpc]
  rw [Finset.sum_add_distrib]
  -- setup costs (Lemma 7)
  have hsetup : ∑ t ∈ Finset.range T, (N.K0 * (if 0 < π.order t () d then 1 else 0)
        + ∑ i, N.K i * (if 0 < π.dispatch t () d i then 1 else 0))
      ≤ ∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
          * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0)
        + N.Kmax * (n + N.L0)
        + ∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then N.K i
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0) := by
    have h5 := hO5 T
    have hreq : ∀ t, (if 0 < t ∧ actE N x c d (t - 1) then ∑ i, N.K i
          * (if PhE N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i
              ∧ PhE N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) < c.S i then 1 else 0) else 0)
        = ∑ i, (if actE N x c d t then N.K i
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0) := by
      intro t
      by_cases h : 0 < t ∧ actE N x c d (t - 1)
      · have ht : actE N x c d t := by
          have := actE_mono N x c d (t - 1) h.2
          rwa [show t - 1 + 1 = t by omega] at this
        rw [if_pos h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_pos ht]
        simp only [XrE, if_neg (show t ≠ 0 by omega), if_pos h.2]
      · rw [if_neg h]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs with ha hb
        · exfalso
          have hX : XrE N x c d t i = c.S i := by
            unfold XrE
            split_ifs with h0 h1
            · rfl
            · exact absurd ⟨by omega, h1⟩ h
            · rfl
          rw [hX] at hb
          exact lt_irrefl _ hb.2
        · simp
        · rfl
    simp_rw [hreq, hord] at h5
    rw [Finset.sum_comm (f := fun t i => (if actE N x c d t then N.K i
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0))] at h5
    have hKm0 : 0 ≤ N.Kmax := by
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
      · simp [Network.Kmax, Real.iSup_of_isEmpty]
      · exact le_trans (hK i) (le_ciSup (Set.finite_range _).bddAbove i)
    rw [Finset.sum_add_distrib]
    simp_rw [hord]
    have e1 : ∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
          * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0)
        = ∑ t ∈ Finset.range T, N.K0 * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0)
          + N.Kmax * ∑ t ∈ Finset.range T,
            (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e1]
    nlinarith
  -- holding and backlog costs (Lemma 8, lead-time shifts)
  have hhold : ∑ t ∈ Finset.range T, (N.h * W t + ∑ i, cH N i (Policy.netInv N x π () d i t))
      ≤ ∑ i, ∑ t ∈ Finset.range (N.L i),
          cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
        + ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
        + ∑ t ∈ Finset.range T, (if t + N.L0 < T then whLoss N.h N.p (YpostE N x c d t
          - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ)) else 0)
        + ∑ i, ∑ t ∈ Finset.range T, (if t + N.L i < T then cH N i (PhE N x c d t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
        + ∑ i, ∑ t ∈ Finset.range T, whLoss N.h N.p (c.a i - PhE N x c d t i) := by
    have hcH0 : ∀ i y, 0 ≤ cH N i y := fun i y =>
      add_nonneg (mul_nonneg (hH i) (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))
    -- retailers: shift each by its lead time
    have hret : ∀ i, ∑ t ∈ Finset.range T, cH N i (Policy.netInv N x π () d i t)
        ≤ ∑ t ∈ Finset.range (N.L i),
            cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
          + ∑ t ∈ Finset.range T, (if t + N.L i < T then cH N i (RP t i
            - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := by
      intro i
      refine (shift_sum_le (fun t => cH N i (Policy.netInv N x π () d i t)) (fun t => hcH0 i _)
        (N.L i) T).trans (le_of_eq ?_)
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        congr 1
        unfold Policy.netInv
        congr 1
        refine Finset.sum_congr rfl fun s hs => ?_
        simp only [Policy.retArrival, if_pos (show s < N.L i by
          have := Finset.mem_range.1 hs; have := Finset.mem_range.1 ht; omega)]
      · refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs
        · rw [netInv_shift]
        · rfl
    -- the echelon: shift by the supplier lead time
    have hE : ∑ t ∈ Finset.range T, whLoss N.h N.p (W t + ∑ i, (RP t i - c.a i))
        ≤ ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
            + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
            - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
          + ∑ t ∈ Finset.range T, (if t + N.L0 < T then whLoss N.h N.p (YpostE N x c d t
            - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ)) else 0) := by
      refine (shift_sum_le (fun t => whLoss N.h N.p (W t + ∑ i, (RP t i - c.a i)))
        (fun t => whLoss_nonneg _ _ _ hh hp) N.L0 T).trans (le_of_eq ?_)
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        have htL : t < N.L0 := Finset.mem_range.1 ht
        congr 1
        simp only [hWdef, hRPdef, Policy.whStock, retPos]
        have e1 : ∑ s ∈ Finset.range (t + 1), Policy.supArrival N x π () d s
            = ∑ s ∈ Finset.range (t + 1), x.supPipe s :=
          Finset.sum_congr rfl fun s hs => by
            simp only [Policy.supArrival, if_pos (show s < N.L0 by
              have := Finset.mem_range.1 hs; omega)]
        have e2 : ∑ s ∈ Finset.range (t + 1), ∑ i, π.dispatch s () d i
            = ∑ i, ∑ s ∈ Finset.range (t + 1), π.dispatch s () d i := Finset.sum_comm
        have e3 : ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
            = ∑ i, ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := Finset.sum_comm
        rw [Finset.sum_sub_distrib, e1, e2, e3]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
      · refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs
        · congr 1
          have hps := pool_shift N x π c.a () d t
          have hpool : poolPos N x π c.a t ((), d) = YpostE N x c d t := by
            unfold poolPos
            rw [Finset.sum_range_succ (fun r => π.order r () d)]
            simp only [hord]
            have hy := YpE_sum N x c d t
            have hc : ∑ r ∈ Finset.range t, ((∑ i, d r i : ℝ≥0) : ℝ)
                = ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ) :=
              Finset.sum_congr rfl fun r _ => NNReal.coe_sum _ _
            rw [hc]
            have h0 : YpE N x c d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
                + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i) := rfl
            linarith
          rw [← hpool]
          simpa [hWdef, hRPdef] using hps
        · rfl
    -- Lemma 8 at every period
    have h8 : ∀ t ∈ Finset.range T, N.h * W t + ∑ i, (if t + N.L i < T then cH N i (RP t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
        ≤ whLoss N.h N.p (W t + ∑ i, (RP t i - c.a i)) + ∑ i, whLoss N.h N.p (c.a i - PhE N x c d t i)
          + ∑ i, (if t + N.L i < T then cH N i (PhE N x c d t i
            - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := by
      intro t _
      exact lemma8_alg N.h N.p hh hp N.H hH (W t) (hO2 t) (PhE N x c d t) (RP t) c.a
        (fun i => ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
        (fun i => hO3 t i) (hO4 t) (fun i => t + N.L i < T)
    have hsum8 := Finset.sum_le_sum h8
    rw [Finset.sum_add_distrib] at hsum8
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum8
    have hret' := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hret i
    rw [Finset.sum_add_distrib] at hret'
    have c1 : ∑ t ∈ Finset.range T, (N.h * W t + ∑ i, cH N i (Policy.netInv N x π () d i t))
        = ∑ t ∈ Finset.range T, N.h * W t
          + ∑ i, ∑ t ∈ Finset.range T, cH N i (Policy.netInv N x π () d i t) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    have c2 : ∑ i, ∑ t ∈ Finset.range T, (if t + N.L i < T then cH N i (RP t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
        = ∑ t ∈ Finset.range T, ∑ i, (if t + N.L i < T then cH N i (RP t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := Finset.sum_comm
    have c3 : ∑ i, ∑ t ∈ Finset.range T, (if t + N.L i < T then cH N i (PhE N x c d t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
        = ∑ t ∈ Finset.range T, ∑ i, (if t + N.L i < T then cH N i (PhE N x c d t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := Finset.sum_comm
    have c4 : ∑ i, ∑ t ∈ Finset.range T, whLoss N.h N.p (c.a i - PhE N x c d t i)
        = ∑ t ∈ Finset.range T, ∑ i, whLoss N.h N.p (c.a i - PhE N x c d t i) := Finset.sum_comm
    rw [c1, c3, c4]
    rw [c2] at hret'
    linarith
  unfold RB
  linarith

end path

/-! ### Expected costs -/

/-- The lead-time cost kernel: integrating a piecewise-linear cost against the law of a sum of
`m` i.i.d. demands. -/
private lemma block_eval (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (m : ℕ) (Hc pc : ℝ) (hHc : 0 ≤ Hc) (hpc : 0 ≤ pc)
    (X : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Hc * max (X - y) 0 + pc * max (-(X - y)) 0)
        ∂((Measure.pi fun _ : Fin m => ρ).map fun w => ∑ j, (w j : ℝ))
      = ENNReal.ofReal (∫ w, (Hc * max (X - ∑ j, (w j : ℝ)) 0 + pc * max (∑ j, (w j : ℝ) - X) 0)
          ∂(Measure.pi fun _ : Fin m => ρ)) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (Hc * max (X - y) 0 + pc * max (-(X - y)) 0) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_map hm (measurable_psum m)]
  simp only [neg_sub]
  rw [ofReal_integral_eq_lintegral_ofReal (nv_integrable _ _ (integrable_psum ρ hρ m) Hc pc X)
    (ae_of_all _ fun w => add_nonneg (mul_nonneg hHc (le_max_right _ _))
      (mul_nonneg hpc (le_max_right _ _)))]

private lemma fL0_eq {n : ℕ} (N : Network n) (X : ℝ) :
    N.fL0 X = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate) (fun w => ∑ j, (w j : ℝ)) N.h N.p X := by
  unfold Network.fL0 nvCost whLoss
  simp only [neg_sub]

private lemma F_eq {n : ℕ} (N : Network n) (i : Fin n) (X : ℝ) :
    N.F i X = nvCost (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) (fun w => ∑ j, (w j : ℝ))
      (N.H i) N.p X := rfl

private lemma fL0_cont {n : ℕ} (N : Network n) (hN : N.Standing) : Continuous N.fL0 := by
  have : N.fL0 = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate) (fun w => ∑ j, (w j : ℝ))
      N.h N.p := funext fun X => fL0_eq N X
  rw [this]
  exact nv_continuous _ _ (integrable_psum _ (integrable_aggregate N hN) _) _ _ hN.h_pos.le hN.p_pos.le

private lemma fL0_lip {n : ℕ} (N : Network n) (hN : N.Standing) (y y' : ℝ) :
    |N.fL0 y - N.fL0 y'| ≤ (N.h + N.p) * |y - y'| := by
  rw [fL0_eq, fL0_eq]
  exact nv_lip _ _ (integrable_psum _ (integrable_aggregate N hN) _) _ _ hN.h_pos.le hN.p_pos.le y y'

private lemma fL0_nonneg {n : ℕ} (N : Network n) (hN : N.Standing) (y : ℝ) : 0 ≤ N.fL0 y := by
  rw [fL0_eq]; exact nv_nonneg _ _ _ _ _ hN.h_pos.le hN.p_pos.le

private lemma mean_agg_pos {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.aggregate := by
  unfold Network.aggregate
  rw [lintegral_map measurable_coe_nnreal_ennreal
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)]
  refine lt_of_lt_of_le (hN.mean_pos ⟨0, hn⟩) (lintegral_mono fun a => ?_)
  simp only [ENNReal.coe_finset_sum]
  exact Finset.single_le_sum (f := fun i => ((a i : ℝ≥0) : ℝ≥0∞)) (fun i _ => zero_le)
    (Finset.mem_univ _)

private lemma mean_marg_pos {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.marginal i := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

private lemma whLoss_le_abs (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p y ≤ (h + p) * |y| := by
  unfold whLoss
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_left hy, max_eq_right (by linarith), abs_of_nonneg hy]; nlinarith
  · rw [max_eq_right hy.le, max_eq_left (by linarith), abs_of_neg hy]; nlinarith

/-- The mirror loss as an `(s,S)` average with no setup cost. -/
private lemma mirror_as_ss (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    ssAvgCost ρ (fun y => whLoss h p (a - y)) 0 s S = mirrorAvg ρ h p s S a := by
  unfold ssAvgCost mirrorAvg ssPeriodCost
  simp only [zero_mul, zero_add]

section expect2

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private lemma YpostE_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => YpostE N x c d t := by
  unfold YpostE
  exact Measurable.ite ((actE_meas N x c t).inter (measurableSet_le (YpE_meas N x c t)
    measurable_const)) measurable_const (YpE_meas N x c t)

private lemma YpostE_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    YpostE N x c d t = YpostE N x c d' t := by
  unfold YpostE
  rw [YpE_dep N x c t d d' h]
  by_cases ha : actE N x c d t
  · simp only [ha, (actE_dep N x c t d d' h).1 ha, true_and]
  · have ha' : ¬ actE N x c d' t := fun h' => ha ((actE_dep N x c t d d' h).2 h')
    simp only [ha, ha', false_and, if_false]

private lemma meas_coord (t : ℕ) (i : Fin n) :
    Measurable fun d : ℕ → DemandVec n => ((d t i : ℝ≥0) : ℝ) :=
  ((measurable_pi_apply i).comp (measurable_pi_apply t)).coe_nnreal_real

/-- The prep-phase position costs grow at most linearly with the demand so far. -/
private lemma prep_pt (hN : N.Standing) (d : ℕ → DemandVec n) (t : ℕ) (ht : ¬ actE N x c d t) :
    N.fL0 (YpE N x c d t) + ∑ i, (N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i))
      ≤ (N.fL0 0 + (N.h + N.p) * (|YpE N x c d 0| + 1)
          + ∑ i, (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
            + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)))
        * (1 + ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)) := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  set Dt := ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) with hDt
  have hD0 : ∀ i, 0 ≤ ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) :=
    fun i => Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _
  have hDt0 : 0 ≤ Dt := Finset.sum_nonneg fun i _ => hD0 i
  have hDi : ∀ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ Dt := fun i =>
    Finset.single_le_sum (f := fun i => ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      (fun i _ => hD0 i) (Finset.mem_univ i)
  -- the supplier
  have hY := YpE_prep N x c d t ht
  have hYsum : ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ) = Dt := Finset.sum_comm
  have hf := fL0_lip N hN (YpE N x c d t) 0
  have habsY : |YpE N x c d t| ≤ |YpE N x c d 0| + Dt := by
    rw [hY, hYsum]
    calc |YpE N x c d 0 - Dt| ≤ |YpE N x c d 0| + |Dt| := abs_sub _ _
      _ = |YpE N x c d 0| + Dt := by rw [abs_of_nonneg hDt0]
  have hs1 : N.fL0 (YpE N x c d t) ≤ N.fL0 0 + (N.h + N.p) * (|YpE N x c d 0| + Dt) := by
    rw [sub_zero] at hf
    have := (abs_le.1 hf).2
    nlinarith
  -- the retailers
  have hret : ∀ i, N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i)
      ≤ (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
        + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1))
        * (1 + Dt) := by
    intro i
    have hHi := (hN.H_pos i).le
    obtain ⟨hF0, -, hFl, -⟩ := F_properties N hN i
    have hP := PhE_prep N x c d t ht i
    set B := x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s with hB
    have habs : |PhE N x c d t i| ≤ |B| + Dt := by
      rw [hP]
      calc |B - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)|
          ≤ |B| + |∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)| := abs_sub _ _
        _ ≤ |B| + Dt := by rw [abs_of_nonneg (hD0 i)]; linarith [hDi i]
    have h1 : N.F i (PhE N x c d t i) ≤ N.F i 0 + (N.H i + N.p) * (|B| + Dt) := by
      have := (abs_le.1 (hFl (PhE N x c d t i) 0)).2
      rw [sub_zero] at this
      nlinarith
    have h2 : whLoss N.h N.p (c.a i - PhE N x c d t i) ≤ (N.h + N.p) * (|c.a i| + |B| + Dt) := by
      refine (whLoss_le_abs _ _ _ hh hp).trans ?_
      have : |c.a i - PhE N x c d t i| ≤ |c.a i| + |B| + Dt := by
        have := abs_sub (c.a i) (PhE N x c d t i)
        linarith
      nlinarith
    have hF0' := hF0 0
    have hab := abs_nonneg B
    have hac := abs_nonneg (c.a i)
    set Ki := N.F i 0 + (N.H i + N.p) * (|B| + 1) + (N.h + N.p) * (|c.a i| + |B| + 1) with hKi
    have hHp : 0 ≤ N.H i + N.p := by linarith
    have hhp : 0 ≤ N.h + N.p := by linarith
    have hk1 : N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i)
        ≤ Ki + (N.H i + N.p + (N.h + N.p)) * Dt := by
      have e1 : (N.H i + N.p) * (|B| + Dt) = (N.H i + N.p) * |B| + (N.H i + N.p) * Dt := by ring
      have e2 : (N.h + N.p) * (|c.a i| + |B| + Dt)
          = (N.h + N.p) * (|c.a i| + |B|) + (N.h + N.p) * Dt := by ring
      have e3 : Ki = N.F i 0 + (N.H i + N.p) * |B| + (N.h + N.p) * (|c.a i| + |B|)
          + (N.H i + N.p + (N.h + N.p)) := by rw [hKi]; ring
      have e4 : (N.H i + N.p + (N.h + N.p)) * Dt = (N.H i + N.p) * Dt + (N.h + N.p) * Dt := by ring
      linarith
    have hk2 : (N.H i + N.p + (N.h + N.p)) * Dt ≤ Ki * Dt := by
      refine mul_le_mul_of_nonneg_right ?_ hDt0
      have : 0 ≤ (N.H i + N.p) * |B| := mul_nonneg hHp hab
      have : 0 ≤ (N.h + N.p) * (|c.a i| + |B|) := mul_nonneg hhp (by linarith)
      rw [hKi]
      nlinarith
    calc N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i)
        ≤ Ki + Ki * Dt := by linarith
      _ = Ki * (1 + Dt) := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hret i
  rw [← Finset.sum_mul] at hsum
  have hf00 := fL0_nonneg N hN 0
  have hY0 := abs_nonneg (YpE N x c d 0)
  set A0 := N.fL0 0 + (N.h + N.p) * (|YpE N x c d 0| + 1) with hA0
  have hhp : 0 ≤ N.h + N.p := by linarith
  have ha1 : N.fL0 (YpE N x c d t) ≤ A0 + (N.h + N.p) * Dt := by
    have : (N.h + N.p) * (|YpE N x c d 0| + Dt) = (N.h + N.p) * |YpE N x c d 0| + (N.h + N.p) * Dt := by
      ring
    rw [hA0]; nlinarith
  have ha2 : (N.h + N.p) * Dt ≤ A0 * Dt := by
    refine mul_le_mul_of_nonneg_right ?_ hDt0
    rw [hA0]
    nlinarith [mul_nonneg hhp hY0]
  have e5 : (A0 + ∑ i, (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
        + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1))) * (1 + Dt)
      = A0 * (1 + Dt) + (∑ i, (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
        + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1))) * (1 + Dt) := by
    ring
  rw [e5]
  have e6 : A0 * (1 + Dt) = A0 + A0 * Dt := by ring
  linarith

end expect2

section expect3

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private lemma coord_le (T s : ℕ) (i : Fin n) :
    ∫⁻ z, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by
  by_cases hs : s < T
  · have e : ∀ z : Fin T → DemandVec n, padHist T z s = z ⟨s, hs⟩ := fun z => by
      simp [padHist, hs]
    simp_rw [e]
    rw [(measurePreserving_eval (fun _ : Fin T => N.μ) (⟨s, hs⟩ : Fin T)).lintegral_comp
      (f := fun a : DemandVec n => ((a i : ℝ≥0) : ℝ≥0∞)) (measurable_pi_apply i).coe_nnreal_ennreal]
  · have e : ∀ z : Fin T → DemandVec n, padHist T z s = 0 := fun z => by simp [padHist, hs]
    simp_rw [e]
    simp

private lemma lin_exp (T k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ))
        ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ 1 + k * ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by
  have hD := measurable_padHist' (α := DemandVec n) T
  have e : ∀ z : Fin T → DemandVec n,
      ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ))
        = 1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) := by
    intro z
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
      NNReal.coe_nonneg _), ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => NNReal.coe_nonneg _]
    exact Finset.sum_congr rfl fun s _ => ENNReal.ofReal_coe_nnreal
  simp_rw [e]
  have hm : ∀ i s, Measurable fun z : Fin T → DemandVec n => ((padHist T z s i : ℝ≥0) : ℝ≥0∞) :=
    fun i s => ((measurable_pi_apply i).comp ((measurable_pi_apply s).comp hD)).coe_nnreal_ennreal
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum (f := fun i (z : Fin T → DemandVec n) =>
      ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ≥0∞)) _
      fun i _ => Finset.measurable_sum _ fun s _ => hm i s]
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum (f := fun s (z : Fin T → DemandVec n) => ((padHist T z s i : ℝ≥0) : ℝ≥0∞))
    _ fun s _ => hm i s]
  calc ∑ s ∈ Finset.range k, ∫⁻ z, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∑ _s ∈ Finset.range k, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ :=
        Finset.sum_le_sum fun s _ => coord_le N T s i
    _ = k * ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by simp

/-- The initial terms (before the prescribed pipelines have arrived) are linear in the demand of
the first `Tpipe` periods. -/
private lemma init_pt (hN : N.Standing) (d : ℕ → DemandVec n) :
    N.Kmax * (n + N.L0)
      + ∑ i, ∑ t ∈ Finset.range (N.L i),
          cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
      + ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
    ≤ (N.Kmax * (n + N.L0)
        + ∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1))
        + (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1)))
      * (1 + ∑ i, ∑ s ∈ Finset.range N.Tpipe, ((d s i : ℝ≥0) : ℝ)) := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hKm0 : 0 ≤ N.Kmax := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · simp [Network.Kmax, Real.iSup_of_isEmpty]
    · exact le_trans (hN.K_nonneg i) (le_ciSup (Set.finite_range _).bddAbove i)
  set Dk := ∑ i, ∑ s ∈ Finset.range N.Tpipe, ((d s i : ℝ≥0) : ℝ) with hDk
  have hD0 : ∀ i k, 0 ≤ ∑ s ∈ Finset.range k, ((d s i : ℝ≥0) : ℝ) :=
    fun i k => Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _
  have hDk0 : 0 ≤ Dk := Finset.sum_nonneg fun i _ => hD0 i _
  have hDle : ∀ i k, k ≤ N.Tpipe → ∑ s ∈ Finset.range k, ((d s i : ℝ≥0) : ℝ) ≤ Dk := by
    intro i k hk
    calc ∑ s ∈ Finset.range k, ((d s i : ℝ≥0) : ℝ)
        ≤ ∑ s ∈ Finset.range N.Tpipe, ((d s i : ℝ≥0) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
            fun s _ _ => NNReal.coe_nonneg _
      _ ≤ Dk := Finset.single_le_sum (f := fun i => ∑ s ∈ Finset.range N.Tpipe, ((d s i : ℝ≥0) : ℝ))
          (fun i _ => hD0 i _) (Finset.mem_univ i)
  -- the retailer terms
  have hRD : ∀ i, ∑ t ∈ Finset.range (N.L i),
      cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
      ≤ (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1))
        * (1 + Dk) := by
    intro i
    have hHp : 0 ≤ N.H i + N.p := by linarith [(hN.H_pos i).le]
    have hR0 : 0 ≤ ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| :=
      Finset.sum_nonneg fun s _ => abs_nonneg _
    have hterm : ∀ t ∈ Finset.range (N.L i),
        cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
        ≤ (N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1) * (1 + Dk) := by
      intro t ht
      have htL := Finset.mem_range.1 ht
      have hL := L_le_Tpipe N i
      have h1 : cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
          ≤ (N.H i + N.p) * |x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))| :=
        whLoss_le_abs _ _ _ (hN.H_pos i).le hp
      have h2 : |x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))|
          ≤ |x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + Dk := by
        rw [Finset.sum_sub_distrib]
        have k1 : |∑ s ∈ Finset.range (t + 1), x.retPipe i s| ≤ ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega)) fun s _ _ => abs_nonneg _)
        have k2 := hDle i (t + 1) (by omega)
        have k3 := hD0 i (t + 1)
        calc |x.I i + (∑ s ∈ Finset.range (t + 1), x.retPipe i s
              - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))|
            ≤ |x.I i| + |∑ s ∈ Finset.range (t + 1), x.retPipe i s|
              + |∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ)| := by
              have := abs_add_le (x.I i) (∑ s ∈ Finset.range (t + 1), x.retPipe i s
                - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))
              have := abs_sub (∑ s ∈ Finset.range (t + 1), x.retPipe i s)
                (∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))
              linarith
          _ ≤ _ := by rw [abs_of_nonneg k3]; linarith
      have h3 : (N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + Dk)
          ≤ (N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1) * (1 + Dk) := by
        have := abs_nonneg (x.I i)
        nlinarith [mul_nonneg hHp (add_nonneg (add_nonneg (abs_nonneg (x.I i)) hR0) zero_le_one),
          mul_nonneg (mul_nonneg hHp (add_nonneg (abs_nonneg (x.I i)) hR0)) hDk0]
      calc _ ≤ _ := h1
        _ ≤ (N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + Dk) :=
            mul_le_mul_of_nonneg_left h2 hHp
        _ ≤ _ := h3
    calc _ ≤ ∑ _t ∈ Finset.range (N.L i),
          (N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1) * (1 + Dk) :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the warehouse terms
  have hRE : ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
      ≤ (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1)) * (1 + Dk) := by
    have hhp : 0 ≤ N.h + N.p := by linarith
    set Q := |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| with hQ
    have hQ0 : 0 ≤ Q := abs_nonneg _
    have hS0 : 0 ≤ ∑ s ∈ Finset.range N.L0, |x.supPipe s| := Finset.sum_nonneg fun s _ => abs_nonneg _
    have hterm : ∀ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
        ≤ (N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s| + Q + 1) * (1 + Dk) := by
      intro t ht
      have htL := Finset.mem_range.1 ht
      have hL0 : N.L0 ≤ N.Tpipe := le_max_left _ _
      have k1 : |∑ s ∈ Finset.range (t + 1), x.supPipe s| ≤ ∑ s ∈ Finset.range N.L0, |x.supPipe s| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun s _ _ => abs_nonneg _)
      have k2 : ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ) ≤ Dk := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i _ => (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun s _ _ => NNReal.coe_nonneg _)
      have k3 : 0 ≤ ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ) :=
        Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
      have k4 : |x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)|
          ≤ |x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s| + Q + Dk := by
        have a1 := abs_sub (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
          (∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ))
        have a2 := abs_add_le (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s)
          (∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
        have a3 := abs_add_le x.W (∑ s ∈ Finset.range (t + 1), x.supPipe s)
        rw [abs_of_nonneg k3] at a1
        linarith
      refine (whLoss_le_abs _ _ _ hh hp).trans ?_
      have := abs_nonneg x.W
      nlinarith [mul_le_mul_of_nonneg_left k4 hhp, mul_nonneg hhp (add_nonneg (add_nonneg
        (add_nonneg (abs_nonneg x.W) hS0) hQ0) zero_le_one),
        mul_nonneg (mul_nonneg hhp (add_nonneg (add_nonneg (abs_nonneg x.W) hS0) hQ0)) hDk0]
    calc _ ≤ ∑ _t ∈ Finset.range N.L0,
          (N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s| + Q + 1) * (1 + Dk) :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hRB0 : N.Kmax * (n + N.L0) ≤ N.Kmax * (n + N.L0) * (1 + Dk) := by
    have : 0 ≤ N.Kmax * (n + N.L0) := mul_nonneg hKm0 (by positivity)
    nlinarith
  have hsumD := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hRD i
  rw [← Finset.sum_mul] at hsumD
  have e : (N.Kmax * (n + N.L0)
        + ∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1))
        + (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1))) * (1 + Dk)
      = N.Kmax * (n + N.L0) * (1 + Dk)
        + (∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1)))
          * (1 + Dk)
        + (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1)) * (1 + Dk) := by
    ring
  rw [e]
  have e2 : ∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1))
        * (1 + Dk)
      = (∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1)))
        * (1 + Dk) := by rw [Finset.sum_mul]
  linarith

end expect3

section final

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private lemma whLoss_cont (h p : ℝ) : Continuous (whLoss h p) := by
  unfold whLoss; fun_prop

private lemma cH_cont (i : Fin n) : Continuous (cH N i) := by
  unfold cH; fun_prop

private lemma F_cont (hN : N.Standing) (i : Fin n) : Continuous (N.F i) := by
  have hL : LipschitzWith (Real.toNNReal (N.H i + N.p)) (N.F i) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [hN.H_pos i, hN.p_pos])]
    exact (F_properties N hN i).2.2.1 y y'
  exact hL.continuous

/-- The pointwise rearrangement: the costs at request positions after the start are the
`(s,S)` cycle costs of the three single-location processes, and before the start they are
linear in the demand so far. -/
private lemma main_pt (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (Cp : ℝ) (hCp0 : 0 ≤ Cp)
    (hCp : ∀ d t, ¬ actE N x c d t → N.fL0 (YpE N x c d t)
      + ∑ i, (N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i))
      ≤ Cp * (1 + ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)))
    (d : ℕ → DemandVec n) (T : ℕ) :
    ENNReal.ofReal (∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
        * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0))
      + ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then N.K i
        * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0))
      + ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, whLoss N.h N.p (c.a i - PhE N x c d t i))
      + ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c d t))
      + ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c d t i))
    ≤ ∑ t ∈ Finset.range T, (if actE N x c d t then ENNReal.ofReal ((N.K0 + N.Kmax)
          * (if YpE N x c d t ≤ c.s0 ∧ YpE N x c d t < c.S0 then 1 else 0)
          + N.fL0 (if YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t)) else 0)
      + ∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then ENNReal.ofReal (N.K i
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
          + N.F i (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)) else 0)
      + ∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then ENNReal.ofReal (0
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
          + whLoss N.h N.p (c.a i - (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)))
          else 0)
      + ENNReal.ofReal Cp * ∑ t ∈ Finset.range T, (if actE N x c d t then 0
          else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))) := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hK0 := hN.K0_nonneg
  have hK := hN.K_nonneg
  have hKm0 : 0 ≤ N.Kmax := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · simp [Network.Kmax, Real.iSup_of_isEmpty]
    · exact le_trans (hK i) (le_ciSup (Set.finite_range _).bddAbove i)
  have hF0 : ∀ i y, 0 ≤ N.F i y := fun i y => (F_properties N hN i).1 y
  have hwl0 : ∀ y, 0 ≤ whLoss N.h N.p y := fun y => whLoss_nonneg _ _ _ hh hp
  have hind : ∀ (K : ℝ), 0 ≤ K → ∀ (q : Prop) [Decidable q], 0 ≤ K * (if q then (1 : ℝ) else 0) :=
    fun K hK q _ => by split_ifs <;> simp [hK]
  have hKK : 0 ≤ N.K0 + N.Kmax := by linarith
  have hRC0 : ∀ i t, 0 ≤ (if actE N x c d t then N.K i * (if XrE N x c d t i ≤ c.s i
      ∧ XrE N x c d t i < c.S i then (1 : ℝ) else 0) else 0) := fun i t => by
    split_ifs <;> simp [hK i]
  -- turn the real sums into sums of `ofReal`
  have r1 : ENNReal.ofReal (∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
        * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0))
      = ∑ t ∈ Finset.range T, ENNReal.ofReal ((N.K0 + N.Kmax)
        * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0)) :=
    ENNReal.ofReal_sum_of_nonneg fun t _ => hind _ hKK _
  have r2 : ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then N.K i
        * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0))
      = ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (if actE N x c d t then N.K i
        * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun t _ => hRC0 i t]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun t _ => hRC0 i t
  have r3 : ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, whLoss N.h N.p (c.a i - PhE N x c d t i))
      = ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (whLoss N.h N.p (c.a i - PhE N x c d t i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun t _ => hwl0 _]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun t _ => hwl0 _
  rw [r1, r2, r3]
  -- everything as one sum over periods
  rw [Finset.sum_comm (f := fun i t => ENNReal.ofReal (if actE N x c d t then N.K i
      * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0)),
    Finset.sum_comm (f := fun i t => ENNReal.ofReal (whLoss N.h N.p (c.a i - PhE N x c d t i))),
    Finset.sum_comm (f := fun i t => ENNReal.ofReal (N.F i (PhE N x c d t i))),
    Finset.sum_comm (f := fun i t => (if actE N x c d t then ENNReal.ofReal (N.K i
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
          + N.F i (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)) else 0)),
    Finset.sum_comm (f := fun i t => (if actE N x c d t then ENNReal.ofReal (0
          * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
          + whLoss N.h N.p (c.a i - (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)))
          else 0)), Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases ha : actE N x c d t
  · -- after the start: equality
    have hpost : ∀ i, PhE N x c d t i
        = if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i :=
      fun i => PhE_post N x c hsS d t ha i
    have hYp : YpostE N x c d t = if YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t := by
      simp only [YpostE, ha, true_and]
    have hord : (if 0 < YpostE N x c d t - YpE N x c d t then (1 : ℝ) else 0)
        = if YpE N x c d t ≤ c.s0 ∧ YpE N x c d t < c.S0 then 1 else 0 := by
      rw [hYp]
      by_cases h1 : YpE N x c d t ≤ c.s0
      · by_cases h2 : YpE N x c d t < c.S0
        · rw [if_pos h1, if_pos (by linarith), if_pos ⟨h1, h2⟩]
        · rw [if_pos h1, if_neg (by linarith), if_neg (fun h => h2 h.2)]
      · rw [if_neg h1, sub_self, if_neg (lt_irrefl 0), if_neg (fun h => h1 h.1)]
    simp only [ha, if_true, if_false, mul_zero, add_zero]
    rw [hord, ← hYp]
    simp_rw [← hpost]
    rw [ENNReal.ofReal_add (hind _ hKK _) (fL0_nonneg N hN _)]
    have e : ∀ i, ENNReal.ofReal (N.K i * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i
          then 1 else 0) + N.F i (PhE N x c d t i))
        = ENNReal.ofReal (N.K i * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i
          then 1 else 0)) + ENNReal.ofReal (N.F i (PhE N x c d t i)) := fun i =>
      ENNReal.ofReal_add (hind _ (hK i) _) (hF0 i _)
    simp only [e, zero_mul, zero_add, Finset.sum_add_distrib]
    exact le_of_eq (by ring)
  · -- before the start: linear in the demand so far
    have hYp : YpostE N x c d t = YpE N x c d t := by simp only [YpostE, ha, false_and, if_false]
    simp only [ha, if_false, if_true, hYp, sub_self, lt_irrefl, mul_zero, ENNReal.ofReal_zero,
      zero_add, Finset.sum_const_zero, add_zero]
    have hb := hCp d t ha
    rw [← ENNReal.ofReal_mul hCp0]
    refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hb)
    rw [ENNReal.ofReal_add (fL0_nonneg N hN _) (Finset.sum_nonneg fun i _ =>
      add_nonneg (hF0 i _) (hwl0 _)), ENNReal.ofReal_sum_of_nonneg fun i _ =>
      add_nonneg (hF0 i _) (hwl0 _)]
    simp only [ENNReal.ofReal_add (hF0 _ _) (hwl0 _), Finset.sum_add_distrib]
    ring

end final

section final2

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private lemma meas_d (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => ((d t i : ℝ≥0) : ℝ) :=
  ((measurable_pi_apply i).comp (measurable_pi_apply t)).coe_nnreal_real

private lemma ind_meas {f : (ℕ → DemandVec n) → ℝ} (hf : Measurable f) (K : ℝ) :
    Measurable fun d => K * (if 0 < f d then (1 : ℝ) else 0) :=
  measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const hf) measurable_const
    measurable_const)

/-- The stopping-time block for the supplier: `𝔼 φ(Ŷ_t - D_{[t,t+L₀)}) = 𝔼 f_{L₀}(Ŷ_t)`. -/
private lemma block_F (hN : N.Standing) (T t : ℕ) (htT : t + N.L0 ≤ T) :
    ∫⁻ z, ENNReal.ofReal (whLoss N.h N.p (YpostE N x c (padHist T z) t
        - ∑ j ∈ Finset.range N.L0, ((∑ i, padHist T z (t + j) i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin T => N.μ)
      = ∫⁻ z, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
        ∂(Measure.pi fun _ : Fin T => N.μ) := by
  have hg : Measurable fun a : DemandVec n => ∑ i, a i := Finset.measurable_sum _ fun i _ =>
    measurable_pi_apply i
  have hG0 : Measurable fun y : ℝ => ENNReal.ofReal (whLoss N.h N.p y) :=
    ENNReal.measurable_ofReal.comp (whLoss_cont N.h N.p).measurable
  have hb := lintegral_block N.μ (fun a => ∑ i, a i) hg T t N.L0 htT
    (fun d => YpostE N x c d t) (YpostE_meas N x c t) (fun d d' h => YpostE_dep N x c t d d' h)
    (fun y => ENNReal.ofReal (whLoss N.h N.p y)) hG0
  simp only at hb
  rw [hb]
  refine lintegral_congr fun z => ?_
  have e := block_eval N.aggregate (integrable_aggregate N hN) N.L0 N.h N.p hN.h_pos.le hN.p_pos.le
    (YpostE N x c (padHist T z) t)
  simp only [whLoss]
  rw [show N.μ.map (fun a => ∑ i, a i) = N.aggregate from rfl, e, fL0_eq]
  rfl

/-- The stopping-time block for retailer `i`: `𝔼 cᵢ(P̂_t - D_{i,[t,t+Lᵢ]}) = 𝔼 Fᵢ(P̂_t)`. -/
private lemma block_G (hN : N.Standing) (i : Fin n) (T t : ℕ) (htT : t + (N.L i + 1) ≤ T) :
    ∫⁻ z, ENNReal.ofReal (cH N i (PhE N x c (padHist T z) t i
        - ∑ j ∈ Finset.range (N.L i + 1), ((padHist T z (t + j) i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin T => N.μ)
      = ∫⁻ z, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i))
        ∂(Measure.pi fun _ : Fin T => N.μ) := by
  have hG0 : Measurable fun y : ℝ => ENNReal.ofReal (cH N i y) :=
    ENNReal.measurable_ofReal.comp (cH_cont N i).measurable
  have hb := lintegral_block N.μ (fun a => a i) (measurable_pi_apply i) T t (N.L i + 1) htT
    (fun d => PhE N x c d t i) (PhE_meas N x c t i) (fun d d' h => PhE_dep N x c t d d' h i)
    (fun y => ENNReal.ofReal (cH N i y)) hG0
  simp only at hb
  rw [hb]
  refine lintegral_congr fun z => ?_
  have e := block_eval (N.marginal i) (integrable_marginal N hN i) (N.L i + 1) (N.H i) N.p
    (hN.H_pos i).le hN.p_pos.le (PhE N x c (padHist T z) t i)
  simp only [cH]
  rw [show N.μ.map (fun a => a i) = N.marginal i from rfl, e]
  rfl

end final2

section final3

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

private lemma pc_nonneg (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i)
    (hs0 : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) :
    0 ≤ Policy.periodCost N x (fifoPolicy N x c).toPolicy () d t := by
  obtain ⟨-, hO2, -, -, -⟩ := fifo_engine_invariants N hN x hx c hsS hs0 d (actE N x c d)
    (fun t => Iff.rfl) (YpE N x c d) rfl (fun t => rfl) (PhE N x c d) (fun i => rfl)
    (fun t i => rfl)
  unfold Policy.periodCost
  have h1 : 0 ≤ N.K0 * (if 0 < (fifoPolicy N x c).toPolicy.order t () d then (1 : ℝ) else 0) :=
    mul_nonneg hN.K0_nonneg (by split_ifs <;> norm_num)
  have h2 : 0 ≤ ∑ i, N.K i * (if 0 < (fifoPolicy N x c).toPolicy.dispatch t () d i then (1 : ℝ)
      else 0) := Finset.sum_nonneg fun i _ => mul_nonneg (hN.K_nonneg i) (by split_ifs <;> norm_num)
  have h3 : 0 ≤ N.h * Policy.whStock N x (fifoPolicy N x c).toPolicy () d t :=
    mul_nonneg hN.h_pos.le (hO2 t)
  have h4 : 0 ≤ ∑ i, (N.H i * max (Policy.netInv N x (fifoPolicy N x c).toPolicy () d i t) 0
      + N.p * max (-Policy.netInv N x (fifoPolicy N x c).toPolicy () d i t) 0) :=
    Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (hN.H_pos i).le (le_max_right _ _))
      (mul_nonneg hN.p_pos.le (le_max_right _ _))
  linarith

private lemma mcomp {β : Type} [MeasurableSpace β] {f : (ℕ → DemandVec n) → β} (hf : Measurable f)
    (T : ℕ) : Measurable fun z : Fin T → DemandVec n => f (padHist T z) :=
  hf.comp (measurable_padHist' (α := DemandVec n) T)

/-- The finite-horizon bound: `𝔼 ∑_{t<T} c_t ≤ T (J₀ + ∑ᵢ (Jᵢ + mirror)) + C`. -/
private lemma fin_bound (hn : 0 < n) (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i)
    (hs0 : c.s0 ≤ c.S0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T : ℕ, expCost N x (fifoPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ T * (ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0
        + ∑ i, (ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i)
          + mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i))) + C := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hK0 := hN.K0_nonneg
  have hK := hN.K_nonneg
  have hKm0 : 0 ≤ N.Kmax := by
    rcases isEmpty_or_nonempty (Fin n) with hn' | ⟨⟨i⟩⟩
    · simp [Network.Kmax, Real.iSup_of_isEmpty]
    · exact le_trans (hK i) (le_ciSup (Set.finite_range _).bddAbove i)
  -- the supplier `(s₀,S₀)` process after the start
  set M0 := x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s + ∑ i, (c.S i - c.a i) with hM0
  have hYstep : ∀ t (d : ℕ → DemandVec n), actE N x c d t → YpE N x c d (t + 1)
      = (if YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t) - ((∑ i, d t i : ℝ≥0) : ℝ) := by
    intro t d h
    show (if actE N x c d t ∧ YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_sum]
    simp only [h, true_and]
  have hY0le : ∀ d : ℕ → DemandVec n, YpE N x c d 0
      - ∑ r ∈ Finset.range 0, ∑ i, ((d r i : ℝ≥0) : ℝ) ≤ M0 → YpE N x c d 0 ≤ M0 := by
    intro d h; simpa using h
  have hYstart : ∀ t (d : ℕ → DemandVec n), actE N x c d t → (t = 0 ∨ ¬ actE N x c d (t - 1)) →
      YpE N x c d t ≤ M0 := by
    intro t d ha hs
    have hprep : YpE N x c d t = YpE N x c d 0 - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ) := by
      rcases hs with h0 | h1
      · subst h0; simp
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
          rcases Nat.eq_zero_or_pos t with h | h
          · subst h; exact absurd ha (by simpa using h1)
          · exact ⟨t - 1, by omega⟩
        simp only [add_tsub_cancel_right] at h1
        show (if actE N x c d t' ∧ YpE N x c d t' ≤ c.s0 then c.S0 else YpE N x c d t')
          - ∑ i, ((d t' i : ℝ≥0) : ℝ) = _
        rw [if_neg (fun hh => h1 hh.1), YpE_prep N x c d t' h1, Finset.sum_range_succ]
        ring
    rw [hprep]
    have hY0 : YpE N x c d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i) := rfl
    rw [hY0, Finset.sum_comm, hM0]
    have hb := ha.2
    have : ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
        - ∑ i, ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) ≤ ∑ i, (c.S i - c.a i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun i _ => by linarith [hb i]
    linarith
  obtain ⟨Cs, hCsf, hCs⟩ := ss_poisson_upper N.μ (fun a => ∑ i, a i)
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) N.aggregate rfl
    (mean_agg_pos hn N hN) N.fL0 (fL0_cont N hN) (fL0_nonneg N hN) (N.K0 + N.Kmax) c.s0 c.S0 M0
    (by linarith) hs0 (fun t d => actE N x c d t) (fun t d => YpE N x c d t)
    (fun t => actE_meas N x c t) (fun t => YpE_meas N x c t)
    (fun t d d' h => actE_dep N x c t d d' h) (fun t d d' h => YpE_dep N x c t d d' h)
    (fun t d h => actE_mono N x c d t h) hYstep
    (fun d h => hYstart 0 d h (Or.inl rfl))
    (fun t d h1 h2 => hYstart (t + 1) d h2 (Or.inr (by simpa using h1)))
  -- the retailer `(sᵢ,Sᵢ)` processes after the start
  have hXs0 : ∀ i (d : ℕ → DemandVec n), actE N x c d 0 → XrE N x c d 0 i ≤ c.S i := fun i d _ => by
    simp [XrE]
  have hXs : ∀ i t (d : ℕ → DemandVec n), ¬ actE N x c d t → actE N x c d (t + 1) →
      XrE N x c d (t + 1) i ≤ c.S i := fun i t d h _ => by
    simp [XrE, h]
  choose Cr hCrf hCr using fun i => ss_poisson_upper N.μ (fun a => a i) (measurable_pi_apply i)
    (N.marginal i) rfl (mean_marg_pos N hN i) (N.F i) (F_cont N hN i) (F_properties N hN i).1
    (N.K i) (c.s i) (c.S i) (c.S i) (hK i) (hsS i) (fun t d => actE N x c d t)
    (fun t d => XrE N x c d t i) (fun t => actE_meas N x c t) (fun t => XrE_meas N x c t i)
    (fun t d d' h => actE_dep N x c t d d' h) (fun t d d' h => XrE_dep N x c t d d' h i)
    (fun t d h => actE_mono N x c d t h) (fun t d h => XrE_step N x c hsS d t h i) (hXs0 i)
    (hXs i)
  choose Cm hCmf hCm using fun i => ss_poisson_upper N.μ (fun a => a i) (measurable_pi_apply i)
    (N.marginal i) rfl (mean_marg_pos N hN i) (fun y => whLoss N.h N.p (c.a i - y))
    ((whLoss_cont N.h N.p).comp (continuous_const.sub continuous_id))
    (fun y => whLoss_nonneg _ _ _ hh hp) 0 (c.s i) (c.S i) (c.S i) le_rfl (hsS i)
    (fun t d => actE N x c d t)
    (fun t d => XrE N x c d t i) (fun t => actE_meas N x c t) (fun t => XrE_meas N x c t i)
    (fun t d d' h => actE_dep N x c t d d' h) (fun t d d' h => XrE_dep N x c t d d' h i)
    (fun t d h => actE_mono N x c d t h) (fun t d h => XrE_step N x c hsS d t h i) (hXs0 i)
    (hXs i)
  -- the preparation phase (Appendix B)
  obtain ⟨Cq, hCqf, hCq⟩ := fifo_prep_bound N.μ hN.mean_pos hN.mean_lt_top N.Tpipe
    (fun i => x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i)
  -- constants
  set Y00 : ℝ := x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
    + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i) with hY00
  set Cp : ℝ := N.fL0 0 + (N.h + N.p) * (|Y00| + 1)
    + ∑ i, (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
      + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)) with hCpdef
  have hCp0 : 0 ≤ Cp := by
    have := fL0_nonneg N hN 0
    have : 0 ≤ ∑ i, (N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)
      + (N.h + N.p) * (|c.a i| + |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + 1)) :=
      Finset.sum_nonneg fun i _ => add_nonneg (add_nonneg ((F_properties N hN i).1 0)
        (mul_nonneg (by linarith [(hN.H_pos i).le]) (by positivity)))
        (mul_nonneg (by linarith) (by positivity))
    have : 0 ≤ (N.h + N.p) * (|Y00| + 1) := mul_nonneg (by linarith) (by positivity)
    linarith
  have hCp : ∀ d t, ¬ actE N x c d t → N.fL0 (YpE N x c d t)
      + ∑ i, (N.F i (PhE N x c d t i) + whLoss N.h N.p (c.a i - PhE N x c d t i))
      ≤ Cp * (1 + ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)) := fun d t ht =>
    prep_pt N x c hN d t ht
  set Ci : ℝ := N.Kmax * (n + N.L0)
        + ∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1))
        + (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1)) with hCidef
  set mm : ℝ≥0∞ := ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ with hmm
  have hmmf : mm ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => (hN.mean_lt_top i).ne
  refine ⟨Cs + ∑ i, Cr i + ∑ i, Cm i + ENNReal.ofReal Cp * Cq
    + ENNReal.ofReal Ci * (1 + N.Tpipe * mm), ?_, fun T => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨hCsf, ENNReal.sum_ne_top.2 fun i _ => hCrf i⟩, ENNReal.sum_ne_top.2 fun i _ => hCmf i⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCqf⟩, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hmmf⟩)⟩
  -- measurability of the ingredients
  have hD := measurable_padHist' (α := DemandVec n) T
  have mY := fun t => YpE_meas N x c t
  have mYp := fun t => YpostE_meas N x c t
  have mP := fun t i => PhE_meas N x c t i
  have mX := fun t i => XrE_meas N x c t i
  have mAct := fun t => actE_meas N x c t
  have mwl : Measurable (whLoss N.h N.p) := (whLoss_cont _ _).measurable
  have mcH : ∀ i, Measurable (cH N i) := fun i => (cH_cont N i).measurable
  have mfL0 : Measurable N.fL0 := (fL0_cont N hN).measurable
  have mF : ∀ i, Measurable (N.F i) := fun i => (F_cont N hN i).measurable
  have mDsum : ∀ t, Measurable fun d : ℕ → DemandVec n =>
      ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) := fun t =>
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun s _ => meas_d s i
  have mXind : ∀ t i, MeasurableSet {d : ℕ → DemandVec n |
      XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i} := fun t i =>
    (measurableSet_le (mX t i) measurable_const).inter (measurableSet_lt (mX t i) measurable_const)
  have mXpost : ∀ t i, Measurable fun d : ℕ → DemandVec n =>
      (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i) := fun t i =>
    Measurable.ite (measurableSet_le (mX t i) measurable_const) measurable_const (mX t i)
  -- the four parts of the pathwise bound
  set fA : (ℕ → DemandVec n) → ℝ := fun d => ∑ t ∈ Finset.range T, (N.K0 + N.Kmax)
      * (if 0 < YpostE N x c d t - YpE N x c d t then 1 else 0) with hfA
  set fC : (ℕ → DemandVec n) → ℝ := fun d => ∑ i, ∑ t ∈ Finset.range T, (if actE N x c d t then N.K i
      * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0) else 0) with hfC
  set fH : (ℕ → DemandVec n) → ℝ := fun d => ∑ i, ∑ t ∈ Finset.range T,
      whLoss N.h N.p (c.a i - PhE N x c d t i) with hfH
  set fF : (ℕ → DemandVec n) → ℝ := fun d => ∑ t ∈ Finset.range T, (if t + N.L0 < T then
      whLoss N.h N.p (YpostE N x c d t - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ))
      else 0) with hfF
  set fG : (ℕ → DemandVec n) → ℝ := fun d => ∑ i, ∑ t ∈ Finset.range T, (if t + N.L i < T then
      cH N i (PhE N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0)
      with hfG
  set fI : (ℕ → DemandVec n) → ℝ := fun d => N.Kmax * (n + N.L0)
      + ∑ i, ∑ t ∈ Finset.range (N.L i),
          cH N i (x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
      + ∑ t ∈ Finset.range N.L0, whLoss N.h N.p (x.W + ∑ s ∈ Finset.range (t + 1), x.supPipe s
          + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
          - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)) with hfI
  have hRB : ∀ d, RB N x c d T = fA d + fC d + fH d + fF d + fG d + fI d := fun d => by
    simp only [RB, hfA, hfC, hfH, hfF, hfG, hfI]; ring
  have mfA : Measurable fun d => ENNReal.ofReal (fA d) :=
    (Finset.measurable_sum _ fun t _ => ind_meas ((mYp t).sub (mY t)) _).ennreal_ofReal
  have mfC : Measurable fun d => ENNReal.ofReal (fC d) :=
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ => Measurable.ite (mAct t)
      (measurable_const.mul (Measurable.ite (mXind t i) measurable_const measurable_const))
      measurable_const).ennreal_ofReal
  have mfH : Measurable fun d => ENNReal.ofReal (fH d) :=
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ =>
      mwl.comp (measurable_const.sub (mP t i))).ennreal_ofReal
  have mSF : Measurable fun d => ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c d t)) :=
    Finset.measurable_sum _ fun t _ => (mfL0.comp (mYp t)).ennreal_ofReal
  have mSG : Measurable fun d => ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c d t i)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ =>
      ((mF i).comp (mP t i)).ennreal_ofReal
  -- step 1: the policy cost and the pathwise bound
  have s1 : expCost N x (fifoPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ ∫⁻ z, ENNReal.ofReal (RB N x c (padHist T z) T) ∂(Measure.pi fun _ : Fin T => N.μ) := by
    unfold expCost
    rw [Measure.dirac_prod]
    refine (lintegral_map_le _ _).trans (lintegral_mono fun z => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => pc_nonneg N x c hN hx hsS hs0 _ t]
    exact ENNReal.ofReal_le_ofReal (path_bound N x c hN hx hsS hs0 _ T)
  -- step 2: split the bound
  have s2 : ∀ z : Fin T → DemandVec n, ENNReal.ofReal (RB N x c (padHist T z) T)
      ≤ (ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) + ENNReal.ofReal (fF (padHist T z))
        + ENNReal.ofReal (fG (padHist T z)) + ENNReal.ofReal (fI (padHist T z)) := fun z => by
    rw [hRB]
    have k : ∀ a b c d e f : ℝ, ENNReal.ofReal (a + b + c + d + e + f)
        ≤ ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d
          + ENNReal.ofReal e + ENNReal.ofReal f := by
      intro a b c d e f
      calc ENNReal.ofReal (a + b + c + d + e + f)
          ≤ ENNReal.ofReal (a + b + c + d + e) + ENNReal.ofReal f := ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (a + b + c + d) + ENNReal.ofReal e + ENNReal.ofReal f := by
            gcongr; exact ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (a + b + c) + ENNReal.ofReal d + ENNReal.ofReal e + ENNReal.ofReal f := by
            gcongr; exact ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (a + b) + ENNReal.ofReal c + ENNReal.ofReal d + ENNReal.ofReal e
            + ENNReal.ofReal f := by gcongr; exact ENNReal.ofReal_add_le
        _ ≤ _ := by gcongr; exact ENNReal.ofReal_add_le
    exact k _ _ _ _ _ _
  -- measurability and nonnegativity of the per-period pieces
  have mSF0 : ∀ t, Measurable fun d : ℕ → DemandVec n =>
      ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) := fun t =>
    Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp (measurable_pi_apply (t + j))).coe_nnreal_real
  have mSG0 : ∀ t i, Measurable fun d : ℕ → DemandVec n =>
      ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ) := fun t i =>
    Finset.measurable_sum _ fun j _ => meas_d (t + j) i
  have mgF : ∀ t, Measurable fun d : ℕ → DemandVec n => (if t + N.L0 < T then
      whLoss N.h N.p (YpostE N x c d t - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ))
      else 0) := fun t =>
    Measurable.ite (MeasurableSet.const _) (mwl.comp ((mYp t).sub (mSF0 t))) measurable_const
  have mgG : ∀ i t, Measurable fun d : ℕ → DemandVec n => (if t + N.L i < T then
      cH N i (PhE N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
      else 0) := fun i t =>
    Measurable.ite (MeasurableSet.const _) ((mcH i).comp ((mP t i).sub (mSG0 t i))) measurable_const
  have hgF0 : ∀ d t, 0 ≤ (if t + N.L0 < T then whLoss N.h N.p (YpostE N x c d t
      - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ)) else 0) := fun d t => by
    split_ifs
    · exact whLoss_nonneg _ _ _ hh hp
    · exact le_rfl
  have hcH0 : ∀ i y, 0 ≤ cH N i y := fun i y =>
    add_nonneg (mul_nonneg (hN.H_pos i).le (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))
  have hgG0 : ∀ d i t, 0 ≤ (if t + N.L i < T then cH N i (PhE N x c d t i
      - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := fun d i t => by
    split_ifs
    · exact hcH0 _ _
    · exact le_rfl
  have mfF : Measurable fun d => ENNReal.ofReal (fF d) :=
    (Finset.measurable_sum _ fun t _ => mgF t).ennreal_ofReal
  have mfG : Measurable fun d => ENNReal.ofReal (fG d) :=
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ => mgG i t).ennreal_ofReal
  have eF : ∀ d, ENNReal.ofReal (fF d) = ∑ t ∈ Finset.range T, ENNReal.ofReal (if t + N.L0 < T then
      whLoss N.h N.p (YpostE N x c d t - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ))
      else 0) := fun d => ENNReal.ofReal_sum_of_nonneg fun t _ => hgF0 d t
  have eG : ∀ d, ENNReal.ofReal (fG d) = ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (if t + N.L i < T then cH N i (PhE N x c d t i
        - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) else 0) := fun d => by
    simp only [hfG]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun t _ => hgG0 d i t]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun t _ => hgG0 d i t
  -- step 3: integrate the four parts separately
  have s3 : ∫⁻ z, ((ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) + ENNReal.ofReal (fF (padHist T z))
        + ENNReal.ofReal (fG (padHist T z)) + ENNReal.ofReal (fI (padHist T z)))
        ∂(Measure.pi fun _ : Fin T => N.μ)
      = ∫⁻ z, (ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ENNReal.ofReal (fF (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ENNReal.ofReal (fG (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ENNReal.ofReal (fI (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ) := by
    have m1 : Measurable fun z : Fin T → DemandVec n => ENNReal.ofReal (fA (padHist T z))
        + ENNReal.ofReal (fC (padHist T z)) + ENNReal.ofReal (fH (padHist T z)) :=
      mcomp ((mfA.add mfC).add mfH) T
    have m2 : Measurable fun z : Fin T → DemandVec n => ENNReal.ofReal (fA (padHist T z))
        + ENNReal.ofReal (fC (padHist T z)) + ENNReal.ofReal (fH (padHist T z))
        + ENNReal.ofReal (fF (padHist T z)) := mcomp (((mfA.add mfC).add mfH).add mfF) T
    have m3 : Measurable fun z : Fin T → DemandVec n => ENNReal.ofReal (fA (padHist T z))
        + ENNReal.ofReal (fC (padHist T z)) + ENNReal.ofReal (fH (padHist T z))
        + ENNReal.ofReal (fF (padHist T z)) + ENNReal.ofReal (fG (padHist T z)) :=
      mcomp ((((mfA.add mfC).add mfH).add mfF).add mfG) T
    rw [lintegral_add_left m3, lintegral_add_left m2, lintegral_add_left m1]
  -- step 4: the supplier lead-time blocks
  have s4 : ∫⁻ z, ENNReal.ofReal (fF (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
        ∂(Measure.pi fun _ : Fin T => N.μ) := by
    have e1 : ∀ z : Fin T → DemandVec n, ENNReal.ofReal (fF (padHist T z)) = ∑ t ∈ Finset.range T,
        ENNReal.ofReal (if t + N.L0 < T then whLoss N.h N.p (YpostE N x c (padHist T z) t
          - ∑ j ∈ Finset.range N.L0, ((∑ i, padHist T z (t + j) i : ℝ≥0) : ℝ)) else 0) :=
      fun z => eF _
    have mg : ∀ t, Measurable fun z : Fin T → DemandVec n => ENNReal.ofReal (if t + N.L0 < T then
        whLoss N.h N.p (YpostE N x c (padHist T z) t
          - ∑ j ∈ Finset.range N.L0, ((∑ i, padHist T z (t + j) i : ℝ≥0) : ℝ)) else 0) :=
      fun t => mcomp (mgF t).ennreal_ofReal T
    have mf : ∀ t, Measurable fun z : Fin T → DemandVec n =>
        ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t)) :=
      fun t => mcomp (mfL0.comp (mYp t)).ennreal_ofReal T
    rw [lintegral_congr e1, lintegral_finsetSum (Finset.range T) fun t _ => mg t,
      lintegral_finsetSum (Finset.range T) fun t _ => mf t]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases h : t + N.L0 < T
    · simp only [h, ↓reduceIte]
      exact (block_F N x c hN T t h.le).le
    · simp only [h, ↓reduceIte, ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
  -- step 5: the retailer lead-time blocks
  have s5 : ∫⁻ z, ENNReal.ofReal (fG (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∫⁻ z, ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i))
        ∂(Measure.pi fun _ : Fin T => N.μ) := by
    have e1 : ∀ z : Fin T → DemandVec n, ENNReal.ofReal (fG (padHist T z)) = ∑ i, ∑ t ∈ Finset.range T,
        ENNReal.ofReal (if t + N.L i < T then cH N i (PhE N x c (padHist T z) t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((padHist T z (t + j) i : ℝ≥0) : ℝ)) else 0) :=
      fun z => eG _
    have mg : ∀ i t, Measurable fun z : Fin T → DemandVec n => ENNReal.ofReal (if t + N.L i < T then
        cH N i (PhE N x c (padHist T z) t i
          - ∑ j ∈ Finset.range (N.L i + 1), ((padHist T z (t + j) i : ℝ≥0) : ℝ)) else 0) :=
      fun i t => mcomp (mgG i t).ennreal_ofReal T
    have mf : ∀ i t, Measurable fun z : Fin T → DemandVec n =>
        ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i)) :=
      fun i t => mcomp ((mF i).comp (mP t i)).ennreal_ofReal T
    rw [lintegral_congr e1,
      lintegral_finsetSum Finset.univ fun i _ => Finset.measurable_sum (Finset.range T) fun t _ => mg i t,
      lintegral_finsetSum Finset.univ fun i _ => Finset.measurable_sum (Finset.range T) fun t _ => mf i t]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lintegral_finsetSum (Finset.range T) fun t _ => mg i t,
      lintegral_finsetSum (Finset.range T) fun t _ => mf i t]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases h : t + N.L i < T
    · simp only [h, ↓reduceIte]
      exact (block_G N x c hN i T t (by omega)).le
    · simp only [h, ↓reduceIte, ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
  -- step 6: the initial terms
  have hCi0 : 0 ≤ Ci := by
    have h1 : 0 ≤ N.Kmax * (n + N.L0) := mul_nonneg hKm0 (by positivity)
    have h2 : 0 ≤ ∑ i, (N.L i : ℝ) * ((N.H i + N.p)
        * (|x.I i| + ∑ s ∈ Finset.range (N.L i), |x.retPipe i s| + 1)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by linarith [(hN.H_pos i).le]) (add_nonneg (add_nonneg (abs_nonneg _)
          (Finset.sum_nonneg fun s _ => abs_nonneg _)) zero_le_one))
    have h3 : 0 ≤ (N.L0 : ℝ) * ((N.h + N.p) * (|x.W| + ∑ s ∈ Finset.range N.L0, |x.supPipe s|
          + |∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)| + 1)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) (add_nonneg (add_nonneg (add_nonneg
        (abs_nonneg _) (Finset.sum_nonneg fun s _ => abs_nonneg _)) (abs_nonneg _)) zero_le_one))
    linarith
  have s6 : ∫⁻ z, ENNReal.ofReal (fI (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ENNReal.ofReal Ci * (1 + N.Tpipe * mm) := by
    calc ∫⁻ z, ENNReal.ofReal (fI (padHist T z)) ∂(Measure.pi fun _ : Fin T => N.μ)
        ≤ ∫⁻ z, ENNReal.ofReal Ci * ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range N.Tpipe,
            ((padHist T z s i : ℝ≥0) : ℝ)) ∂(Measure.pi fun _ : Fin T => N.μ) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul hCi0]
          exact ENNReal.ofReal_le_ofReal (init_pt N x c hN (padHist T z))
      _ = ENNReal.ofReal Ci * ∫⁻ z, ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range N.Tpipe,
            ((padHist T z s i : ℝ≥0) : ℝ)) ∂(Measure.pi fun _ : Fin T => N.μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Ci * (1 + N.Tpipe * mm) := by
          gcongr
          exact lin_exp N T N.Tpipe
  -- step 7: recombine and apply the pointwise rearrangement
  have s7 : ∫⁻ z, (ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
          ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i))
          ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∫⁻ z, (ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))
          + ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
          + ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i)))
          ∂(Measure.pi fun _ : Fin T => N.μ) := by
    refine le_trans ?_ (le_lintegral_add _ _)
    exact add_le_add (le_lintegral_add _ _) le_rfl
  set PS : (Fin T → DemandVec n) → ℝ≥0∞ := fun z => ∑ t ∈ Finset.range T,
    (if actE N x c (padHist T z) t then ENNReal.ofReal ((N.K0 + N.Kmax)
      * (if YpE N x c (padHist T z) t ≤ c.s0 ∧ YpE N x c (padHist T z) t < c.S0 then 1 else 0)
      + N.fL0 (if YpE N x c (padHist T z) t ≤ c.s0 then c.S0 else YpE N x c (padHist T z) t))
      else 0) with hPS
  set PR : Fin n → (Fin T → DemandVec n) → ℝ≥0∞ := fun i z => ∑ t ∈ Finset.range T,
    (if actE N x c (padHist T z) t then ENNReal.ofReal (N.K i
      * (if XrE N x c (padHist T z) t i ≤ c.s i ∧ XrE N x c (padHist T z) t i < c.S i then 1 else 0)
      + N.F i (if XrE N x c (padHist T z) t i ≤ c.s i then c.S i else XrE N x c (padHist T z) t i))
      else 0) with hPR
  set PM : Fin n → (Fin T → DemandVec n) → ℝ≥0∞ := fun i z => ∑ t ∈ Finset.range T,
    (if actE N x c (padHist T z) t then ENNReal.ofReal (0
      * (if XrE N x c (padHist T z) t i ≤ c.s i ∧ XrE N x c (padHist T z) t i < c.S i then 1 else 0)
      + whLoss N.h N.p (c.a i - (if XrE N x c (padHist T z) t i ≤ c.s i then c.S i
        else XrE N x c (padHist T z) t i))) else 0) with hPM
  set PQ : (Fin T → DemandVec n) → ℝ≥0∞ := fun z => ∑ t ∈ Finset.range T,
    (if actE N x c (padHist T z) t then 0
      else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist T z s i : ℝ≥0) : ℝ))) with hPQ
  have s8 : ∀ z : Fin T → DemandVec n, ENNReal.ofReal (fA (padHist T z))
        + ENNReal.ofReal (fC (padHist T z)) + ENNReal.ofReal (fH (padHist T z))
        + ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
        + ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i))
      ≤ PS z + ∑ i, PR i z + ∑ i, PM i z + ENNReal.ofReal Cp * PQ z := fun z =>
    main_pt N x c hN hsS Cp hCp0 hCp (padHist T z) T
  have mSd : Measurable fun d : ℕ → DemandVec n => ∑ t ∈ Finset.range T,
      (if actE N x c d t then ENNReal.ofReal ((N.K0 + N.Kmax)
        * (if YpE N x c d t ≤ c.s0 ∧ YpE N x c d t < c.S0 then 1 else 0)
        + N.fL0 (if YpE N x c d t ≤ c.s0 then c.S0 else YpE N x c d t)) else 0) :=
    Finset.measurable_sum _ fun t _ => Measurable.ite (mAct t)
      ((measurable_const.mul (Measurable.ite ((measurableSet_le (mY t) measurable_const).inter
        (measurableSet_lt (mY t) measurable_const)) measurable_const measurable_const)).add
        (mfL0.comp (Measurable.ite (measurableSet_le (mY t) measurable_const) measurable_const
          (mY t)))).ennreal_ofReal measurable_const
  have mRd : ∀ i, Measurable fun d : ℕ → DemandVec n => ∑ t ∈ Finset.range T,
      (if actE N x c d t then ENNReal.ofReal (N.K i
        * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
        + N.F i (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)) else 0) := fun i =>
    Finset.measurable_sum _ fun t _ => Measurable.ite (mAct t)
      ((measurable_const.mul (Measurable.ite (mXind t i) measurable_const measurable_const)).add
        ((mF i).comp (mXpost t i))).ennreal_ofReal measurable_const
  have mMd : ∀ i, Measurable fun d : ℕ → DemandVec n => ∑ t ∈ Finset.range T,
      (if actE N x c d t then ENNReal.ofReal (0
        * (if XrE N x c d t i ≤ c.s i ∧ XrE N x c d t i < c.S i then 1 else 0)
        + whLoss N.h N.p (c.a i - (if XrE N x c d t i ≤ c.s i then c.S i else XrE N x c d t i)))
        else 0) := fun i =>
    Finset.measurable_sum _ fun t _ => Measurable.ite (mAct t)
      ((measurable_const.mul (Measurable.ite (mXind t i) measurable_const measurable_const)).add
        (mwl.comp (measurable_const.sub (mXpost t i)))).ennreal_ofReal measurable_const
  have mPS : Measurable PS := mcomp mSd T
  have mPR : ∀ i, Measurable (PR i) := fun i => mcomp (mRd i) T
  have mPM : ∀ i, Measurable (PM i) := fun i => mcomp (mMd i) T
  have s9 : ∫⁻ z, (PS z + ∑ i, PR i z + ∑ i, PM i z + ENNReal.ofReal Cp * PQ z)
        ∂(Measure.pi fun _ : Fin T => N.μ)
      = ∫⁻ z, PS z ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∑ i, ∫⁻ z, PR i z ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∑ i, ∫⁻ z, PM i z ∂(Measure.pi fun _ : Fin T => N.μ)
        + ENNReal.ofReal Cp * ∫⁻ z, PQ z ∂(Measure.pi fun _ : Fin T => N.μ) := by
    have m1 : Measurable fun z => PS z + ∑ i, PR i z :=
      mPS.add (Finset.measurable_sum _ fun i _ => mPR i)
    have m2 : Measurable fun z => PS z + ∑ i, PR i z + ∑ i, PM i z :=
      m1.add (Finset.measurable_sum _ fun i _ => mPM i)
    rw [lintegral_add_left m2, lintegral_add_left m1, lintegral_add_left mPS,
      lintegral_finsetSum _ fun i _ => mPR i, lintegral_finsetSum _ fun i _ => mPM i,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 8: the single-location bounds
  have hS : ∫⁻ z, PS z ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ T * ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0 + Cs := hCs T T le_rfl
  have hR : ∀ i, ∫⁻ z, PR i z ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ T * ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i) + Cr i := fun i =>
    hCr i T T le_rfl
  have hM : ∀ i, ∫⁻ z, PM i z ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ T * mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i) + Cm i := fun i => by
    rw [← mirror_as_ss]
    exact hCm i T T le_rfl
  have hact_iff : ∀ (d : ℕ → DemandVec n) t, actE N x c d t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i
        ≤ ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)) := fun d t => by
    unfold actE
    exact and_congr Iff.rfl (forall_congr' fun i => by constructor <;> intro h <;> linarith)
  have hQ : ∫⁻ z, PQ z ∂(Measure.pi fun _ : Fin T => N.μ) ≤ Cq := by
    refine le_trans (le_of_eq ?_) (hCq T T le_rfl)
    refine lintegral_congr fun z => Finset.sum_congr rfl fun t _ => ?_
    by_cases h : actE N x c (padHist T z) t
    · rw [if_pos h, if_pos ((hact_iff _ t).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hact_iff _ t).2 h'))]
  -- step 9: assemble
  calc expCost N x (fifoPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ ∫⁻ z, ENNReal.ofReal (RB N x c (padHist T z) T) ∂(Measure.pi fun _ : Fin T => N.μ) := s1
    _ ≤ ∫⁻ z, ((ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) + ENNReal.ofReal (fF (padHist T z))
        + ENNReal.ofReal (fG (padHist T z)) + ENNReal.ofReal (fI (padHist T z)))
        ∂(Measure.pi fun _ : Fin T => N.μ) := lintegral_mono s2
    _ = _ := s3
    _ ≤ ∫⁻ z, (ENNReal.ofReal (fA (padHist T z)) + ENNReal.ofReal (fC (padHist T z))
          + ENNReal.ofReal (fH (padHist T z))) ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.fL0 (YpostE N x c (padHist T z) t))
          ∂(Measure.pi fun _ : Fin T => N.μ)
        + ∫⁻ z, ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (PhE N x c (padHist T z) t i))
          ∂(Measure.pi fun _ : Fin T => N.μ)
        + ENNReal.ofReal Ci * (1 + N.Tpipe * mm) :=
      add_le_add (add_le_add (add_le_add le_rfl s4) s5) s6
    _ ≤ ∫⁻ z, (PS z + ∑ i, PR i z + ∑ i, PM i z + ENNReal.ofReal Cp * PQ z)
          ∂(Measure.pi fun _ : Fin T => N.μ) + ENNReal.ofReal Ci * (1 + N.Tpipe * mm) :=
      add_le_add (s7.trans (lintegral_mono s8)) le_rfl
    _ = _ := by rw [s9]
    _ ≤ (T * ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0 + Cs)
          + ∑ i, (T * ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i) + Cr i)
          + ∑ i, (T * mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i) + Cm i)
          + ENNReal.ofReal Cp * Cq + ENNReal.ofReal Ci * (1 + N.Tpipe * mm) := by
      refine add_le_add (add_le_add (add_le_add (add_le_add hS (Finset.sum_le_sum fun i _ => hR i))
        (Finset.sum_le_sum fun i _ => hM i)) ?_) le_rfl
      gcongr
    _ = _ := by
      simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      ring

end final3

/-- Base stock `(S,S)`: the pre-action position never exceeds `S`. -/
private lemma ssPre_SS_bound (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    have ih := ssPre_SS_bound S d t
    show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) ≤ S
    rw [if_pos ih]
    linarith [NNReal.coe_nonneg (d t)]

/-- With `s = S = a` the mirror loss vanishes. -/
private lemma mirrorAvg_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p S : ℝ) :
    mirrorAvg ρ h p S S S = 0 := by
  have e : ∀ T (z : Fin T → ℝ≥0) t,
      ENNReal.ofReal (whLoss h p (S - ssPost S S (padHist T z) t)) = 0 := by
    intro T z t
    have : ssPost S S (padHist T z) t = S := if_pos (ssPre_SS_bound S _ t)
    rw [this, sub_self]
    simp [whLoss]
  simp [mirrorAvg, e]

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (x : InitState n) (hx : x.Valid) (c : FIFOChoice n) (hc : IsFIFOChoice N c) :
    (fifoPolicy N x c).avgCost N x ≤ N.J0 (N.K0 + N.Kmax) + ∑ i, N.augCost i (c.s i) (c.S i) := by
  obtain ⟨hcK, hc0, hs0, hJ0⟩ := hc
  have hsS : ∀ i, c.s i ≤ c.S i := by
    intro i
    rcases (hN.K_nonneg i).lt_or_eq with hK | hK
    · obtain ⟨sh, Sh, s', S', hco, hbw, hsel, -⟩ := hcK i hK
      rcases hsel with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · rw [h1, h2]; exact hco.1.le
      · rw [h1, h2]; exact hbw.2.1.le
    · exact (hc0 i hK.symm).1.le
  have hmir : ∀ i, mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)
      ≤ mirrorCost (N.marginal i) N.h N.p (c.s i) (c.S i) := by
    intro i
    rcases (hN.K_nonneg i).lt_or_eq with hK | hK
    · obtain ⟨sh, Sh, s', S', -, -, -, hm⟩ := hcK i hK
      exact hm.le
    · obtain ⟨h1, -, h3⟩ := hc0 i hK.symm
      rw [h1, h3, mirrorAvg_SS]
      exact zero_le
  obtain ⟨C, hCf, hC⟩ := fin_bound N x c hn hN hx hsS hs0
  set G := ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0
    + ∑ i, (ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i)
      + mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)) with hG
  have hGle : G ≤ N.J0 (N.K0 + N.Kmax) + ∑ i, N.augCost i (c.s i) (c.S i) :=
    add_le_add (le_of_eq hJ0) (Finset.sum_le_sum fun i _ => add_le_add le_rfl (hmir i))
  unfold DetPolicy.avgCost OWMR.avgCost
  calc Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹
          * expCost N x (fifoPolicy N x c).toPolicy (Measure.dirac ()) T) Filter.atTop
      ≤ Filter.limsup (fun T : ℕ => G + (T : ℝ≥0∞)⁻¹ * C) Filter.atTop := by
        refine Filter.limsup_le_limsup ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with T hT
        have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
        calc (T : ℝ≥0∞)⁻¹ * expCost N x (fifoPolicy N x c).toPolicy (Measure.dirac ()) T
            ≤ (T : ℝ≥0∞)⁻¹ * (T * G + C) := by gcongr; exact hC T
          _ = G + (T : ℝ≥0∞)⁻¹ * C := by
            rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
    _ ≤ Filter.limsup (fun _ : ℕ => G) Filter.atTop :=
        limsup_add_tendsto_zero (fun _ => G) (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * C) (by
          simpa using ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hCf))
    _ = G := Filter.limsup_const G
    _ ≤ _ := hGle
