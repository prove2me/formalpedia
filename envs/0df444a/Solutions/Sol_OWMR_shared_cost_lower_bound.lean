-- Prove2me | solution 1 for OWMR.shared_cost_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T04:29:16.953072+00:00
-- url     : https://prove2.me/submissions/82500625-e760-44aa-979e-0c4ce503ce28

import Theorems.Thm_OWMR_sl_subsolution
import Theorems.Thm_OWMR_sl_adapted_bound
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
Proposition 3 (shared-cost lower bound): for every real `γ > 1`,
`J₀(γ K₀) + (γ - 1) ∑ᵢ Jᵢ(γ Kᵢ/(γ - 1)) ≤ γ OPT`.

Fix an admissible policy (nonanticipative, measurable, feasible, possibly randomized). For each
retailer `i`, the position `Pᵢ,t` (net inventory plus everything dispatched to `i` by period
`t`) is a single-location position process driven by `i`'s demands; the pooled position
`Ỹ_t = W + ∑ᵢ (Pᵢ - 𝔼 Zᵢ) + pipeline` is one driven by aggregate demand and supplier orders.
Lemma 1 (`sl_subsolution`, `sl_adapted_bound`) bounds `γ - 1` copies of each retailer's
holding/backlog cost `Fᵢ(Pᵢ,t)` with `γ Kᵢ` per dispatch, and one copy of the pooled cost
`f_{L₀}(Ỹ_t)` with `γ K₀` per supplier order, over finite horizons with constants independent of
the horizon. The independence of later demands gives `𝔼 f_{L₀}(Ỹ_t) = 𝔼 φ(Ẽ_{t+L₀})` and
`𝔼 Fᵢ(Pᵢ,t) = 𝔼 [Hᵢ Iᵢ⁺ + p Iᵢ⁻](t + Lᵢ)`, and Jensen with `Hᵢ ≥ h` and subadditivity of
`φ` give `φ(Ẽ_t) ≤ h W_t + ∑ᵢ Fᵢ(Pᵢ,t)`. Summing, `γ` times the physical cost over
`T + L₀ + ∑ Lᵢ` periods dominates the two lower bounds, and dividing by the horizon gives the
claim for the `limsup` average, then for `OPT`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

section

variable {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]

omit [MeasurableSpace U] in
private lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [MeasurableSpace α] [MeasurableSpace U] in
private lemma padHist_insertNth_lt {M : ℕ} (i : Fin (M + 1)) (a b : α) (z : Fin M → α) (s : ℕ)
    (hs : s < i.val) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) s = padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z) s := by
  have hsM : s < M + 1 := lt_trans hs i.2
  have hsM' : s < M := lt_of_lt_of_le hs (Nat.lt_succ_iff.1 i.2)
  simp only [padHist, dif_pos hsM]
  have he : (⟨s, hsM⟩ : Fin (M + 1)) = i.succAbove ⟨s, hsM'⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp [Fin.lt_def, hs]
  rw [he, Fin.insertNth_apply_succAbove (α := fun _ => α), Fin.insertNth_apply_succAbove (α := fun _ => α)]

omit [MeasurableSpace α] [MeasurableSpace U] in
private lemma padHist_insertNth_self {M : ℕ} (i : Fin (M + 1)) (a : α) (z : Fin M → α) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) i.val = a := by
  simp only [padHist, dif_pos i.2]
  exact Fin.insertNth_apply_same (α := fun _ => α) i a z

/-- Resampling one coordinate: if `Φ (u, d)` depends on `d` only through the coordinates before
`t`, then the `t`-th demand is independent of it. -/
private lemma lintegral_coord (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [SFinite ν]
    (N t : ℕ) (ht : t < N) (Φ : U × (ℕ → α) → α → ℝ≥0∞)
    (hΦ : Measurable fun p : (U × (ℕ → α)) × α => Φ p.1 p.2)
    (hdep : ∀ (u : U) (d d' : ℕ → α) (a : α), (∀ s < t, d s = d' s) → Φ (u, d) a = Φ (u, d') a) :
    ∫⁻ ω, Φ (ω.1, padHist N ω.2) (padHist N ω.2 t) ∂(ν.prod (Measure.pi fun _ : Fin N => μ))
      = ∫⁻ ω, ∫⁻ a, Φ (ω.1, padHist N ω.2) a ∂μ ∂(ν.prod (Measure.pi fun _ : Fin N => μ)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hD : Measurable fun z : Fin (M + 1) → α => padHist (M + 1) z := measurable_padHist' _
  have hm1 : Measurable fun ω : U × (Fin (M + 1) → α) =>
      Φ (ω.1, padHist (M + 1) ω.2) (padHist (M + 1) ω.2 t) := by
    have h2 : Measurable fun ω : U × (Fin (M + 1) → α) => padHist (M + 1) ω.2 t :=
      (measurable_pi_apply t).comp (hD.comp measurable_snd)
    exact hΦ.comp ((measurable_fst.prodMk (hD.comp measurable_snd)).prodMk h2)
  have hm2 : Measurable fun ω : U × (Fin (M + 1) → α) =>
      ∫⁻ a, Φ (ω.1, padHist (M + 1) ω.2) a ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (U × (Fin (M + 1) → α)) × α =>
      Φ (p.1.1, padHist (M + 1) p.1.2) p.2)
      (hΦ.comp (((measurable_fst.comp measurable_fst).prodMk
        (hD.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  rw [lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hm2.aemeasurable]
  refine lintegral_congr fun u => ?_
  set i : Fin (M + 1) := ⟨t, ht⟩ with hi
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => α) i with he
  have hsymm : ∀ p : α × (Fin M → α), e.symm p = Fin.insertNth (α := fun _ => α) i p.1 p.2 := fun p => rfl
  -- transport both sides through `e`
  have key : ∀ F : (Fin (M + 1) → α) → ℝ≥0∞,
      ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (M + 1) => μ)
        = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin M => μ)) := by
    intro F
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  -- independence of the earlier coordinates from the inserted value
  have hind : ∀ (a b : α) (z : Fin M → α) (c : α),
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c
        = Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z)) c := by
    intro a b z c
    exact hdep u _ _ c fun s hs => padHist_insertNth_lt i a b z s (by simpa [hi] using hs)
  have hins : Measurable fun p : α × (Fin M → α) => Fin.insertNth (α := fun _ => α) i p.1 p.2 := e.symm.measurable
  have hG : Measurable fun p : α × (Fin M → α) =>
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2)) p.1 :=
    hΦ.comp ((measurable_const.prodMk (hD.comp hins)).prodMk measurable_fst)
  rw [key, key]
  simp only [hsymm]
  have hl : ∀ p : α × (Fin M → α), padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2) t = p.1 :=
    fun p => padHist_insertNth_self i p.1 p.2
  simp only [hl]
  rw [lintegral_prod_symm _ hG.aemeasurable]
  have hc : ∀ (a : α) (z : Fin M → α),
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c ∂μ
        = ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ := fun a z =>
    lintegral_congr fun c => hind a c z c
  simp only [hc]
  have hH : Measurable fun z : Fin M → α =>
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin M → α) × α =>
      Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.2 p.1)) p.2)
      (hΦ.comp ((measurable_const.prodMk (hD.comp (hins.comp
        (measurable_snd.prodMk measurable_fst)))).prodMk measurable_snd))
  have hprod := lintegral_prod (μ := μ) (ν := Measure.pi fun _ : Fin M => μ)
    (fun p : α × (Fin M → α) =>
      ∫⁻ c, Φ (u, padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c p.2)) c ∂μ)
    (hH.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]

end

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

private lemma nv_convex (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (nvCost P X H p) := by
  refine ⟨convex_univ, fun y _ y' _ a c ha hc hac => ?_⟩
  simp only [smul_eq_mul]
  unfold nvCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((nv_integrable P X hX H p y).const_mul a)
      ((nv_integrable P X hX H p y').const_mul c)]
  refine integral_mono (nv_integrable P X hX H p _)
    (((nv_integrable P X hX H p y).const_mul a).add ((nv_integrable P X hX H p y').const_mul c))
    fun b => ?_
  have hs : a * X b + c * X b = X b := by rw [← add_mul, hac, one_mul]
  have k1 : max (a * y + c * y' - X b) 0 ≤ a * max (y - X b) 0 + c * max (y' - X b) 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (y - X b) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (y' - X b) 0) hc
    linarith
  have k2 : max (X b - (a * y + c * y')) 0 ≤ a * max (X b - y) 0 + c * max (X b - y') 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y') 0) hc
    linarith
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  simp only
  linarith

private lemma nv_anti (hX : Integrable X P) (hX0 : ∀ b, 0 ≤ X b) (H p : ℝ) (hp : 0 ≤ p) :
    AntitoneOn (nvCost P X H p) (Set.Iic 0) := by
  intro y hy y' hy' hyy'
  simp only [Set.mem_Iic] at hy hy'
  unfold nvCost
  refine integral_mono (nv_integrable P X hX H p y') (nv_integrable P X hX H p y) fun b => ?_
  have e1 : max (y - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e2 : max (y' - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e3 : max (X b - y) 0 = X b - y := max_eq_left (by linarith [hX0 b])
  have e4 : max (X b - y') 0 = X b - y' := max_eq_left (by linarith [hX0 b])
  simp only [e1, e2, e3, e4]
  nlinarith

private lemma nv_coercive (hX : Integrable X P) (H p : ℝ) (hH : 0 < H) (hp : 0 < p) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ nvCost P X H p y := by
  intro C
  set c := ∫ b, X b ∂P
  set m := min H p with hm
  have hm0 : 0 < m := lt_min hH hp
  refine ⟨|c| + max C 0 / m, fun y hy => ?_⟩
  have hlow := nv_lower P X hX H p y hH.le hp.le
  have hyc : max C 0 / m ≤ |y - c| := by
    have := abs_sub_abs_le_abs_sub y c
    linarith
  have hmc : max C 0 ≤ m * |y - c| := by
    rw [div_le_iff₀ hm0] at hyc
    linarith
  have hkey : m * |y - c| ≤ nvCost P X H p y := by
    rcases le_or_gt c y with h | h
    · rw [abs_of_nonneg (by linarith)]
      calc m * (y - c) ≤ H * (y - c) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
        _ ≤ _ := hlow.1
    · rw [abs_of_neg (by linarith)]
      calc m * -(y - c) = m * (c - y) := by ring
        _ ≤ p * (c - y) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ ≤ _ := hlow.2
  linarith [le_max_left C 0]

/-- Jensen at the warehouse rate: `φ(y - 𝔼X) ≤ 𝔼[H (y - X)⁺ + p (X - y)⁺]` when `h ≤ H`. -/
private lemma whLoss_le_nv (hX : Integrable X P) (h H p y : ℝ) (hhH : h ≤ H) (hh : 0 ≤ h)
    (hp : 0 ≤ p) : whLoss h p (y - ∫ b, X b ∂P) ≤ nvCost P X H p y := by
  have hlow := nv_lower P X hX H p y (by linarith) hp
  unfold whLoss
  rcases le_or_gt 0 (y - ∫ b, X b ∂P) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)]
    have : h * (y - ∫ b, X b ∂P) ≤ H * (y - ∫ b, X b ∂P) := mul_le_mul_of_nonneg_right hhH h0
    linarith [hlow.1]
  · rw [max_eq_right h0.le, max_eq_left (by linarith)]
    have e : -(y - ∫ b, X b ∂P) = ∫ b, X b ∂P - y := by ring
    rw [e]
    linarith [hlow.2]

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

/-! ### Blocks of later demands -/

section block

variable {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]

/-- The sum of the `m` demands of periods `t, …, t+m-1` is independent of everything observed
before period `t`. -/
private lemma lintegral_block (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [SFinite ν]
    (g : α → ℝ≥0) (hg : Measurable g) (TT t : ℕ) :
    ∀ (m : ℕ), t + m ≤ TT → ∀ (X : U × (ℕ → α) → ℝ), Measurable X →
      (∀ (u : U) (d d' : ℕ → α), (∀ s < t, d s = d' s) → X (u, d) = X (u, d')) →
      ∀ (G0 : ℝ → ℝ≥0∞), Measurable G0 →
      ∫⁻ ω, G0 (X (ω.1, padHist TT ω.2)
          - ∑ j ∈ Finset.range m, (g (padHist TT ω.2 (t + j)) : ℝ))
          ∂(ν.prod (Measure.pi fun _ : Fin TT => μ))
        = ∫⁻ ω, ∫⁻ y, G0 (X (ω.1, padHist TT ω.2) - y)
            ∂((Measure.pi fun _ : Fin m => μ.map g).map fun z => ∑ j, (z j : ℝ))
          ∂(ν.prod (Measure.pi fun _ : Fin TT => μ)) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  intro m
  induction m with
  | zero =>
    intro _ X _ _ G0 hG0
    refine lintegral_congr fun ω => ?_
    rw [lintegral_law_zero (μ.map g) (F := fun y => G0 (X (ω.1, padHist TT ω.2) - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    simp
  | succ m ih =>
    intro htm X hX hXdep G0 hG0
    have hgs : ∀ j, Measurable fun d : ℕ → α => (g (d (t + j)) : ℝ) := fun j =>
      (hg.comp (measurable_pi_apply (t + j))).coe_nnreal_real
    have hS : Measurable fun d : ℕ → α => ∑ j ∈ Finset.range m, (g (d (t + j)) : ℝ) :=
      Finset.measurable_sum _ fun j _ => hgs j
    -- peel off the demand of period `t + m`
    set Φ : U × (ℕ → α) → α → ℝ≥0∞ := fun ω a =>
      G0 (X ω - ∑ j ∈ Finset.range m, (g (ω.2 (t + j)) : ℝ) - (g a : ℝ)) with hΦ
    have hΦm : Measurable fun q : (U × (ℕ → α)) × α => Φ q.1 q.2 :=
      hG0.comp (((hX.comp measurable_fst).sub (hS.comp (measurable_snd.comp measurable_fst))).sub
        (hg.comp measurable_snd).coe_nnreal_real)
    have hΦdep : ∀ (u : U) (d d' : ℕ → α) (a : α), (∀ s < t + m, d s = d' s) →
        Φ (u, d) a = Φ (u, d') a := by
      intro u d d' a h
      simp only [hΦ]
      rw [hXdep u d d' (fun s hs => h s (by omega))]
      congr 3
      exact Finset.sum_congr rfl fun j hj => by
        rw [h (t + j) (by have := Finset.mem_range.1 hj; omega)]
    have hstep := lintegral_coord μ ν TT (t + m) (by omega) Φ hΦm hΦdep
    have hL : ∀ ω : U × (Fin TT → α), G0 (X (ω.1, padHist TT ω.2)
        - ∑ j ∈ Finset.range (m + 1), (g (padHist TT ω.2 (t + j)) : ℝ))
        = Φ (ω.1, padHist TT ω.2) (padHist TT ω.2 (t + m)) := by
      intro ω
      simp only [hΦ, Finset.sum_range_succ]
      congr 1
      ring
    simp_rw [hL]
    rw [hstep]
    -- the one-step kernel
    set G1 : ℝ → ℝ≥0∞ := fun y => ∫⁻ a, G0 (y - (g a : ℝ)) ∂μ with hG1
    have hG1m : Measurable G1 :=
      Measurable.lintegral_prod_right' (f := fun q : ℝ × α => G0 (q.1 - (g q.2 : ℝ)))
        (hG0.comp (measurable_fst.sub (hg.comp measurable_snd).coe_nnreal_real))
    have hih := ih (by omega) X hX hXdep G1 hG1m
    have hrw : ∀ ω : U × (Fin TT → α), ∫⁻ a, Φ (ω.1, padHist TT ω.2) a ∂μ
        = G1 (X (ω.1, padHist TT ω.2)
          - ∑ j ∈ Finset.range m, (g (padHist TT ω.2 (t + j)) : ℝ)) := fun ω => rfl
    simp_rw [hrw]
    rw [hih]
    refine lintegral_congr fun ω => ?_
    -- `law_{m+1} = ρ * law_m`
    set x0 := X (ω.1, padHist TT ω.2)
    rw [lintegral_law_succ (μ.map g) m (F := fun y => G0 (x0 - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    have hswap : ∫⁻ y, G1 (x0 - y)
        ∂((Measure.pi fun _ : Fin m => μ.map g).map fun z => ∑ j, (z j : ℝ))
        = ∫⁻ b, ∫⁻ y, G0 (x0 - y - (b : ℝ))
          ∂((Measure.pi fun _ : Fin m => μ.map g).map fun z => ∑ j, (z j : ℝ)) ∂(μ.map g) := by
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

private lemma whStock_nonneg {n : ℕ} {U : Type} (N : Network n) (x : InitState n)
    (π : Policy n U) (hfeas : π.Feasible N x) (u : U) (d : ℕ → DemandVec n) (t : ℕ) :
    0 ≤ Policy.whStock N x π u d t := by
  have h := (hfeas u d t).2.2
  have e : Policy.whStock N x π u d t
      = Policy.whAvailable N x π u d t - ∑ i, π.dispatch t u d i := by
    unfold Policy.whStock Policy.whAvailable
    rw [Finset.sum_range_succ]
    ring
  linarith

section meas

variable {n : ℕ} {U : Type} [MeasurableSpace U] (N : Network n) (x : InitState n)
  (π : Policy n U) (hm : π.IsMeasurable)

include hm

private lemma meas_order (t : ℕ) : Measurable fun ω : U × (ℕ → DemandVec n) => π.order t ω.1 ω.2 :=
  (hm t).1

private lemma meas_dispatch (t : ℕ) (i : Fin n) :
    Measurable fun ω : U × (ℕ → DemandVec n) => π.dispatch t ω.1 ω.2 i :=
  (hm t).2 i

omit hm in
private lemma meas_dem (r : ℕ) (i : Fin n) :
    Measurable fun ω : U × (ℕ → DemandVec n) => ((ω.2 r i : ℝ≥0) : ℝ) :=
  ((measurable_pi_apply i).comp ((measurable_pi_apply r).comp measurable_snd)).coe_nnreal_real

private lemma meas_supArrival (s : ℕ) :
    Measurable fun ω : U × (ℕ → DemandVec n) => Policy.supArrival N x π ω.1 ω.2 s := by
  unfold Policy.supArrival
  by_cases h : s < N.L0
  · simp only [if_pos h]
    exact measurable_const
  · simp only [if_neg h]
    exact meas_order π hm _

private lemma meas_retArrival (i : Fin n) (s : ℕ) :
    Measurable fun ω : U × (ℕ → DemandVec n) => Policy.retArrival N x π ω.1 ω.2 i s := by
  unfold Policy.retArrival
  by_cases h : s < N.L i
  · simp only [if_pos h]
    exact measurable_const
  · simp only [if_neg h]
    exact meas_dispatch π hm _ i

private lemma meas_whStock (t : ℕ) :
    Measurable fun ω : U × (ℕ → DemandVec n) => Policy.whStock N x π ω.1 ω.2 t := by
  unfold Policy.whStock
  exact measurable_const.add (Finset.measurable_sum _ fun s _ =>
    (meas_supArrival N x π hm s).sub (Finset.measurable_sum _ fun i _ => meas_dispatch π hm s i))

private lemma meas_netInv (i : Fin n) (t : ℕ) :
    Measurable fun ω : U × (ℕ → DemandVec n) => Policy.netInv N x π ω.1 ω.2 i t := by
  unfold Policy.netInv
  exact measurable_const.add (Finset.measurable_sum _ fun s _ =>
    (meas_retArrival N x π hm i s).sub (meas_dem s i))

private lemma meas_retPos (i : Fin n) (t : ℕ) : Measurable (retPos N x π i t) := by
  unfold retPos
  exact (measurable_const.add (Finset.measurable_sum _ fun r _ => meas_dispatch π hm r i)).sub
    (Finset.measurable_sum _ fun r _ => meas_dem r i)

private lemma meas_poolPos (cZ : Fin n → ℝ) (t : ℕ) : Measurable (poolPos N x π cZ t) := by
  unfold poolPos
  refine (measurable_const.add (Finset.measurable_sum _ fun r _ => meas_order π hm r)).sub
    (Finset.measurable_sum _ fun r _ => ?_)
  have : Measurable fun ω : U × (ℕ → DemandVec n) => ∑ i, ((ω.2 r i : ℝ≥0) : ℝ) :=
    Finset.measurable_sum _ fun i _ => meas_dem r i
  simpa [NNReal.coe_sum] using this

end meas

private lemma retPos_dep {n : ℕ} {U : Type} (N : Network n) (x : InitState n) (π : Policy n U)
    (hna : π.Nonanticipative) (i : Fin n) (t : ℕ) (u : U) (d d' : ℕ → DemandVec n)
    (h : ∀ s < t, d s = d' s) : retPos N x π i t (u, d) = retPos N x π i t (u, d') := by
  unfold retPos
  have h1 : ∑ r ∈ Finset.range (t + 1), π.dispatch r u d i
      = ∑ r ∈ Finset.range (t + 1), π.dispatch r u d' i :=
    Finset.sum_congr rfl fun r hr => by
      rw [(hna r u d d' fun s hs => h s (by have := Finset.mem_range.1 hr; omega)).2]
  have h2 : ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) = ∑ r ∈ Finset.range t, ((d' r i : ℝ≥0) : ℝ) :=
    Finset.sum_congr rfl fun r hr => by rw [h r (Finset.mem_range.1 hr)]
  simp only
  rw [h1, h2]

private lemma poolPos_dep {n : ℕ} {U : Type} (N : Network n) (x : InitState n) (π : Policy n U)
    (hna : π.Nonanticipative) (cZ : Fin n → ℝ) (t : ℕ) (u : U) (d d' : ℕ → DemandVec n)
    (h : ∀ s < t, d s = d' s) : poolPos N x π cZ t (u, d) = poolPos N x π cZ t (u, d') := by
  unfold poolPos
  have h1 : ∑ r ∈ Finset.range (t + 1), π.order r u d = ∑ r ∈ Finset.range (t + 1), π.order r u d' :=
    Finset.sum_congr rfl fun r hr => by
      rw [(hna r u d d' fun s hs => h s (by have := Finset.mem_range.1 hr; omega)).1]
  have h2 : ∑ r ∈ Finset.range t, ((∑ i, d r i : ℝ≥0) : ℝ)
      = ∑ r ∈ Finset.range t, ((∑ i, d' r i : ℝ≥0) : ℝ) :=
    Finset.sum_congr rfl fun r hr => by rw [h r (Finset.mem_range.1 hr)]
  simp only
  rw [h1, h2]

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

private lemma ind_nonneg (K : ℝ) (hK : 0 ≤ K) (c : Prop) [Decidable c] :
    0 ≤ K * (if c then (1 : ℝ) else 0) := by
  split_ifs <;> simp [hK]

/-- `∑_{t<T} G(t + k) ≤ ∑_{u<M} G u` when `T + k ≤ M`. -/
private lemma sum_shift_le (G : ℕ → ℝ≥0∞) (T k M : ℕ) (h : T + k ≤ M) :
    ∑ t ∈ Finset.range T, G (t + k) ≤ ∑ u ∈ Finset.range M, G u := by
  calc ∑ t ∈ Finset.range T, G (t + k) = ∑ t ∈ Finset.range T, G (k + t) :=
        Finset.sum_congr rfl fun t _ => by rw [add_comm]
    _ ≤ ∑ u ∈ Finset.range k, G u + ∑ t ∈ Finset.range T, G (k + t) := le_add_self
    _ = ∑ u ∈ Finset.range (k + T), G u := (Finset.sum_range_add G k T).symm
    _ ≤ ∑ u ∈ Finset.range M, G u :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-! ### The allocation of `γ` copies of physical cost, over a finite horizon -/

private lemma alloc_bound {n : ℕ} (N : Network n) (hN : N.Standing) (hH : ∀ i, N.h ≤ N.H i)
    (x : InitState n) (γ : ℝ) (hγ : 1 < γ) {U : Type} [MeasurableSpace U] (ν : Measure U)
    [IsProbabilityMeasure ν] (π : Policy n U)
    (hπ : π.Nonanticipative ∧ π.IsMeasurable ∧ π.Feasible N x)
    (J0 : ℝ) (v0 : ℝ → ℝ) (hv0m : Measurable v0) (hv0b : ∀ y, -(γ * N.K0) ≤ v0 y ∧ v0 y ≤ 0)
    (hv0s : ∀ y, J0 ≤ N.fL0 y + ∫ a, v0 (y - ((∑ i, a i : ℝ≥0) : ℝ)) ∂N.μ - v0 y)
    (Jr : Fin n → ℝ) (vr : Fin n → ℝ → ℝ) (hvrm : ∀ i, Measurable (vr i))
    (hvrb : ∀ i y, -(γ * N.K i / (γ - 1)) ≤ vr i y ∧ vr i y ≤ 0)
    (hvrs : ∀ i y, Jr i ≤ N.F i y + ∫ a, vr i (y - ((a i : ℝ≥0) : ℝ)) ∂N.μ - vr i y)
    (T : ℕ) :
    ENNReal.ofReal (T * J0)
      + ENNReal.ofReal (γ - 1) * ∑ i, ENNReal.ofReal (((T + N.L0 : ℕ) : ℝ) * Jr i)
      ≤ ENNReal.ofReal γ * expCost N x π ν (T + N.L0 + ∑ i, N.L i)
        + (ENNReal.ofReal (γ * N.K0)
          + ENNReal.ofReal (γ - 1) * ∑ i, ENNReal.ofReal (γ * N.K i / (γ - 1))) := by
  obtain ⟨hna, hmeas, hfeas⟩ := hπ
  have hγ0 : 0 ≤ γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  have hK0 : 0 ≤ N.K0 := hN.K0_nonneg
  have hKi : ∀ i, 0 ≤ N.K i := hN.K_nonneg
  have hh : 0 < N.h := hN.h_pos
  have hp : 0 < N.p := hN.p_pos
  have hHi : ∀ i, 0 < N.H i := hN.H_pos
  set TT := T + N.L0 + ∑ i, N.L i with hTT
  set P := ν.prod (Measure.pi fun _ : Fin TT => N.μ) with hP
  have hLle : ∀ i, N.L i ≤ ∑ j, N.L j := fun i =>
    Finset.single_le_sum (f := fun j => N.L j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  -- lead-time demands and newsvendor forms
  have hintM : ∀ i, Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) := fun i =>
    integrable_psum _ (integrable_marginal N hN i) _
  have hintA : Integrable (fun z : Fin N.L0 → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin N.L0 => N.aggregate) :=
    integrable_psum _ (integrable_aggregate N hN) _
  have hFnv : ∀ i, N.F i = nvCost (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
      (fun z => ∑ j, (z j : ℝ)) (N.H i) N.p := fun i => rfl
  have hfnv : N.fL0 = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate)
      (fun z => ∑ j, (z j : ℝ)) N.h N.p := by
    funext y
    unfold Network.fL0 nvCost whLoss
    congr 1
    funext z
    rw [neg_sub]
  have hFc : ∀ i, Continuous (N.F i) := fun i => by
    rw [hFnv i]
    exact nv_continuous _ _ (hintM i) _ _ (hHi i).le hp.le
  have hfc : Continuous N.fL0 := by
    rw [hfnv]
    exact nv_continuous _ _ hintA _ _ hh.le hp.le
  have hF0 : ∀ i y, 0 ≤ N.F i y := fun i y => by
    rw [hFnv i]
    exact nv_nonneg _ _ _ _ _ (hHi i).le hp.le
  have hf0 : ∀ y, 0 ≤ N.fL0 y := fun y => by
    rw [hfnv]
    exact nv_nonneg _ _ _ _ _ hh.le hp.le
  set cZ : Fin n → ℝ := fun i =>
    ∫ z, ∑ j, (z j : ℝ) ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) with hcZ
  -- the history map and the per-period pieces
  set Dm : U × (Fin TT → DemandVec n) → U × (ℕ → DemandVec n) :=
    fun ω => (ω.1, padHist TT ω.2) with hDm
  have hDmm : Measurable Dm := measurable_fst.prodMk ((measurable_padHist' TT).comp measurable_snd)
  have hord : ∀ t, Measurable fun ω : U × (ℕ → DemandVec n) => π.order t ω.1 ω.2 :=
    meas_order π hmeas
  have hdis : ∀ t i, Measurable fun ω : U × (ℕ → DemandVec n) => π.dispatch t ω.1 ω.2 i :=
    meas_dispatch π hmeas
  have hwhL : Continuous (whLoss N.h N.p) := by
    unfold whLoss
    fun_prop
  -- the per-period pieces of physical cost
  set s0 : ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (N.K0 * (if 0 < π.order t ω.1 ω.2 then 1 else 0)) with hs0
  set sr : Fin n → ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun i t ω =>
    ENNReal.ofReal (N.K i * (if 0 < π.dispatch t ω.1 ω.2 i then 1 else 0)) with hsr
  set wc : ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (N.h * Policy.whStock N x π ω.1 ω.2 t) with hwc
  set rr : Fin n → ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun i t ω =>
    ENNReal.ofReal (N.H i * max (Policy.netInv N x π ω.1 ω.2 i t) 0
      + N.p * max (-Policy.netInv N x π ω.1 ω.2 i t) 0) with hrr
  set fr : Fin n → ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun i t ω =>
    ENNReal.ofReal (N.F i (retPos N x π i t ω)) with hfr
  set f0 : ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (N.fL0 (poolPos N x π cZ t ω)) with hf0d
  set e0 : ℕ → U × (ℕ → DemandVec n) → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (whLoss N.h N.p (Policy.whStock N x π ω.1 ω.2 t
      + ∑ i, (retPos N x π i t ω - cZ i))) with he0
  have hs0m : ∀ t, Measurable (s0 t) := fun t => ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const (hord t))
      measurable_const measurable_const))
  have hsrm : ∀ i t, Measurable (sr i t) := fun i t => ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const (hdis t i))
      measurable_const measurable_const))
  have hwcm : ∀ t, Measurable (wc t) := fun t =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (meas_whStock N x π hmeas t))
  have hrrm : ∀ i t, Measurable (rr i t) := fun i t => ENNReal.measurable_ofReal.comp
    ((measurable_const.mul ((meas_netInv N x π hmeas i t).max measurable_const)).add
      (measurable_const.mul ((meas_netInv N x π hmeas i t).neg.max measurable_const)))
  have hfrm : ∀ i t, Measurable (fr i t) := fun i t => ENNReal.measurable_ofReal.comp
    ((hFc i).measurable.comp (meas_retPos N x π hmeas i t))
  have hf0m : ∀ t, Measurable (f0 t) := fun t => ENNReal.measurable_ofReal.comp
    (hfc.measurable.comp (meas_poolPos N x π hmeas cZ t))
  -- (1) the expected physical cost, piece by piece
  have hA1 : expCost N x π ν TT = ∑ t ∈ Finset.range TT, ∫⁻ ω, s0 t (Dm ω) ∂P
      + ∑ i, ∑ t ∈ Finset.range TT, ∫⁻ ω, sr i t (Dm ω) ∂P
      + ∑ t ∈ Finset.range TT, ∫⁻ ω, wc t (Dm ω) ∂P
      + ∑ i, ∑ t ∈ Finset.range TT, ∫⁻ ω, rr i t (Dm ω) ∂P := by
    unfold expCost
    have hpt : ∀ (ω : U × (Fin TT → DemandVec n)) (t : ℕ),
        ENNReal.ofReal (π.periodCost N x ω.1 (padHist TT ω.2) t)
          = s0 t (Dm ω) + ∑ i, sr i t (Dm ω) + wc t (Dm ω) + ∑ i, rr i t (Dm ω) := by
      intro ω t
      have hW := whStock_nonneg N x π hfeas ω.1 (padHist TT ω.2) t
      have h1 := ind_nonneg N.K0 hK0 (0 < π.order t ω.1 (padHist TT ω.2))
      have h2 : ∀ i, 0 ≤ N.K i * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then (1 : ℝ) else 0) :=
        fun i => ind_nonneg _ (hKi i) _
      have h3 : 0 ≤ N.h * Policy.whStock N x π ω.1 (padHist TT ω.2) t := mul_nonneg hh.le hW
      have h4 : ∀ i, 0 ≤ N.H i * max (Policy.netInv N x π ω.1 (padHist TT ω.2) i t) 0
          + N.p * max (-Policy.netInv N x π ω.1 (padHist TT ω.2) i t) 0 := fun i =>
        add_nonneg (mul_nonneg (hHi i).le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
      have h12 := add_nonneg h1 (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => h2 i)
      unfold Policy.periodCost
      rw [ENNReal.ofReal_add (add_nonneg h12 h3) (Finset.sum_nonneg fun i _ => h4 i),
        ENNReal.ofReal_add h12 h3, ENNReal.ofReal_add h1 (Finset.sum_nonneg fun i _ => h2 i),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => h2 i),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => h4 i)]
    simp_rw [hpt]
    have hm4 : ∀ t, Measurable fun ω : U × (Fin TT → DemandVec n) =>
        s0 t (Dm ω) + ∑ i, sr i t (Dm ω) + wc t (Dm ω) + ∑ i, rr i t (Dm ω) := fun t =>
      ((((hs0m t).comp hDmm).add (Finset.measurable_sum _ fun i _ => (hsrm i t).comp hDmm)).add
        ((hwcm t).comp hDmm)).add (Finset.measurable_sum _ fun i _ => (hrrm i t).comp hDmm)
    rw [lintegral_finsetSum _ fun t _ => hm4 t]
    have hsplit : ∀ t, ∫⁻ ω, (s0 t (Dm ω) + ∑ i, sr i t (Dm ω) + wc t (Dm ω)
        + ∑ i, rr i t (Dm ω)) ∂P
        = ∫⁻ ω, s0 t (Dm ω) ∂P + ∑ i, ∫⁻ ω, sr i t (Dm ω) ∂P + ∫⁻ ω, wc t (Dm ω) ∂P
          + ∑ i, ∫⁻ ω, rr i t (Dm ω) ∂P := by
      intro t
      rw [lintegral_add_left (f := fun ω => s0 t (Dm ω) + ∑ i, sr i t (Dm ω) + wc t (Dm ω))
          ((((hs0m t).comp hDmm).add (Finset.measurable_sum _ fun i _ =>
            (hsrm i t).comp hDmm)).add ((hwcm t).comp hDmm)),
        lintegral_add_left (f := fun ω => s0 t (Dm ω) + ∑ i, sr i t (Dm ω))
          (((hs0m t).comp hDmm).add (Finset.measurable_sum _ fun i _ => (hsrm i t).comp hDmm)),
        lintegral_add_left (f := fun ω => s0 t (Dm ω)) ((hs0m t).comp hDmm),
        lintegral_finsetSum (f := fun i ω => sr i t (Dm ω)) _ fun i _ => (hsrm i t).comp hDmm,
        lintegral_finsetSum (f := fun i ω => rr i t (Dm ω)) _ fun i _ => (hrrm i t).comp hDmm]
    rw [Finset.sum_congr rfl fun t _ => hsplit t]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_comm (s := Finset.range TT) (t := Finset.univ) (f := fun t i =>
        ∫⁻ ω, sr i t (Dm ω) ∂P),
      Finset.sum_comm (s := Finset.range TT) (t := Finset.univ) (f := fun t i =>
        ∫⁻ ω, rr i t (Dm ω) ∂P)]
  -- `Fᵢ` and `f_{L₀}` as lower integrals of the period loss
  have hfL0lint : ∀ y, ENNReal.ofReal (N.fL0 y) = ∫⁻ z, ENNReal.ofReal
      (whLoss N.h N.p (y - ∑ j, (z j : ℝ))) ∂(Measure.pi fun _ : Fin N.L0 => N.aggregate) := by
    intro y
    have hint : Integrable (fun z : Fin N.L0 → ℝ≥0 => whLoss N.h N.p (y - ∑ j, (z j : ℝ)))
        (Measure.pi fun _ : Fin N.L0 => N.aggregate) := by
      refine (nv_integrable _ _ hintA N.h N.p y).congr (ae_of_all _ fun z => ?_)
      simp only [whLoss, neg_sub]
    unfold Network.fL0
    exact ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun z => whLoss_nonneg _ _ _ hh.le hp.le)
  have hFlint : ∀ i y, ENNReal.ofReal (N.F i y) = ∫⁻ z, ENNReal.ofReal
      (N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (-(y - ∑ j, (z j : ℝ))) 0)
        ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) := by
    intro i y
    have hint := nv_integrable _ _ (hintM i) (N.H i) N.p y
    have e : ∀ z : Fin (N.L i + 1) → ℝ≥0,
        N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (-(y - ∑ j, (z j : ℝ))) 0
          = N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0 := fun z => by
      rw [neg_sub]
    simp_rw [e]
    unfold Network.F
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z =>
      add_nonneg (mul_nonneg (hHi i).le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _)))
  have hmsum : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  -- (2) the pooled cost is the expected warehouse-rate loss `L₀` periods later
  have hA4 : ∀ t, t < T → ∫⁻ ω, f0 t (Dm ω) ∂P = ∫⁻ ω, e0 (t + N.L0) (Dm ω) ∂P := by
    intro t ht
    have hrw : ∀ ω : U × (Fin TT → DemandVec n), e0 (t + N.L0) (Dm ω)
        = ENNReal.ofReal (whLoss N.h N.p (poolPos N x π cZ t (ω.1, padHist TT ω.2)
          - ∑ j ∈ Finset.range N.L0,
            (((fun a : DemandVec n => ∑ i, a i) (padHist TT ω.2 (t + j)) : ℝ≥0) : ℝ))) := by
      intro ω
      show ENNReal.ofReal (whLoss N.h N.p (Policy.whStock N x π ω.1 (padHist TT ω.2) (t + N.L0)
        + ∑ i, (retPos N x π i (t + N.L0) (ω.1, padHist TT ω.2) - cZ i))) = _
      rw [pool_shift]
    rw [lintegral_congr hrw, lintegral_block N.μ ν (fun a => ∑ i, a i) hmsum TT t N.L0 (by omega)
      (poolPos N x π cZ t) (meas_poolPos N x π hmeas cZ t)
      (fun u d d' h => poolPos_dep N x π hna cZ t u d d' h)
      (fun w => ENNReal.ofReal (whLoss N.h N.p w)) (ENNReal.measurable_ofReal.comp hwhL.measurable)]
    refine lintegral_congr fun ω => ?_
    show ENNReal.ofReal (N.fL0 (poolPos N x π cZ t (ω.1, padHist TT ω.2))) = _
    rw [hfL0lint, lintegral_map (f := fun y => ENNReal.ofReal (whLoss N.h N.p
      (poolPos N x π cZ t (ω.1, padHist TT ω.2) - y)))
      (ENNReal.measurable_ofReal.comp (hwhL.measurable.comp (measurable_const.sub measurable_id)))
      (measurable_psum N.L0)]
    rfl
  -- (3) each retailer's cost is its expected holding and backlog cost `Lᵢ` periods later
  have hA6 : ∀ i u, u < T + N.L0 → ∫⁻ ω, fr i u (Dm ω) ∂P = ∫⁻ ω, rr i (u + N.L i) (Dm ω) ∂P := by
    intro i u hu
    have hrw : ∀ ω : U × (Fin TT → DemandVec n), rr i (u + N.L i) (Dm ω)
        = ENNReal.ofReal (N.H i * max (retPos N x π i u (ω.1, padHist TT ω.2)
            - ∑ j ∈ Finset.range (N.L i + 1),
              (((fun a : DemandVec n => a i) (padHist TT ω.2 (u + j)) : ℝ≥0) : ℝ)) 0
          + N.p * max (-(retPos N x π i u (ω.1, padHist TT ω.2)
            - ∑ j ∈ Finset.range (N.L i + 1),
              (((fun a : DemandVec n => a i) (padHist TT ω.2 (u + j)) : ℝ≥0) : ℝ))) 0) := by
      intro ω
      show ENNReal.ofReal (N.H i * max (Policy.netInv N x π ω.1 (padHist TT ω.2) i (u + N.L i)) 0
        + N.p * max (-Policy.netInv N x π ω.1 (padHist TT ω.2) i (u + N.L i)) 0) = _
      rw [netInv_shift]
    have hG : Measurable fun w : ℝ => ENNReal.ofReal (N.H i * max w 0 + N.p * max (-w) 0) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.mul (measurable_id.max measurable_const)).add
        (measurable_const.mul (measurable_id.neg.max measurable_const)))
    rw [lintegral_congr hrw, lintegral_block N.μ ν (fun a => a i) (measurable_pi_apply i) TT u
      (N.L i + 1) (by have := hLle i; omega) (retPos N x π i u) (meas_retPos N x π hmeas i u)
      (fun uu d d' h => retPos_dep N x π hna i u uu d d' h)
      (fun w => ENNReal.ofReal (N.H i * max w 0 + N.p * max (-w) 0)) hG]
    refine lintegral_congr fun ω => ?_
    show ENNReal.ofReal (N.F i (retPos N x π i u (ω.1, padHist TT ω.2))) = _
    rw [hFlint, lintegral_map (f := fun y => ENNReal.ofReal
      (N.H i * max (retPos N x π i u (ω.1, padHist TT ω.2) - y) 0
        + N.p * max (-(retPos N x π i u (ω.1, padHist TT ω.2) - y)) 0))
      (hG.comp (measurable_const.sub measurable_id)) (measurable_psum _)]
    rfl
  -- (4) Jensen and subadditivity: `φ(Ẽ) ≤ h W + ∑ᵢ Fᵢ(Pᵢ)`
  have hA5 : ∀ u ω, e0 u ω ≤ wc u ω + ∑ i, fr i u ω := by
    intro u ω
    have hW := whStock_nonneg N x π hfeas ω.1 ω.2 u
    have hjen : ∀ i, whLoss N.h N.p (retPos N x π i u ω - cZ i)
        ≤ N.F i (retPos N x π i u ω) := fun i => by
      rw [hFnv i]
      exact whLoss_le_nv _ _ (hintM i) N.h (N.H i) N.p _ (hH i) hh.le hp.le
    have hWl : whLoss N.h N.p (Policy.whStock N x π ω.1 ω.2 u)
        = N.h * Policy.whStock N x π ω.1 ω.2 u := by
      unfold whLoss
      rw [max_eq_left hW, max_eq_right (by linarith)]
      ring
    have hreal : whLoss N.h N.p (Policy.whStock N x π ω.1 ω.2 u
        + ∑ i, (retPos N x π i u ω - cZ i))
        ≤ N.h * Policy.whStock N x π ω.1 ω.2 u + ∑ i, N.F i (retPos N x π i u ω) :=
      calc _ ≤ whLoss N.h N.p (Policy.whStock N x π ω.1 ω.2 u)
            + whLoss N.h N.p (∑ i, (retPos N x π i u ω - cZ i)) := whLoss_add _ _ _ _ hh.le hp.le
        _ ≤ whLoss N.h N.p (Policy.whStock N x π ω.1 ω.2 u)
            + ∑ i, whLoss N.h N.p (retPos N x π i u ω - cZ i) :=
          add_le_add le_rfl (whLoss_sum _ _ _ hh.le hp.le _)
        _ ≤ _ := by
          rw [hWl]
          exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => hjen i)
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ∑ i, ENNReal.ofReal _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hF0 i _),
      ← ENNReal.ofReal_add (mul_nonneg hh.le hW) (Finset.sum_nonneg fun i _ => hF0 i _)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- (5) Lemma 1 for the pooled supplier problem: one copy of `f_{L₀}` and `γ K₀` per order
  have hsup : ENNReal.ofReal (T * J0) ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (γ * N.K0 * (if 0 < π.order t ω.1 (padHist TT ω.2) then 1 else 0)
        + N.fL0 (poolPos N x π cZ t (ω.1, padHist TT ω.2))) ∂P + ENNReal.ofReal (γ * N.K0) :=
    sl_adapted_bound N.μ ν (fun a => ∑ i, a i) hmsum π.order
      (fun t u d d' h => (hna t u d d' h).1) hord (fun t u d => (hfeas u d t).1)
      (x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - cZ i))
      N.fL0 hfc.measurable hf0 (γ * N.K0) J0 v0 hv0m hv0b hv0s T TT (by omega)
  have hS0T : ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (γ * N.K0 * (if 0 < π.order t ω.1 (padHist TT ω.2) then 1 else 0)
        + N.fL0 (poolPos N x π cZ t (ω.1, padHist TT ω.2))) ∂P
      = ENNReal.ofReal γ * ∑ t ∈ Finset.range T, ∫⁻ ω, s0 t (Dm ω) ∂P
        + ∑ t ∈ Finset.range T, ∫⁻ ω, f0 t (Dm ω) ∂P := by
    have hpt : ∀ (ω : U × (Fin TT → DemandVec n)) (t : ℕ), ENNReal.ofReal
        (γ * N.K0 * (if 0 < π.order t ω.1 (padHist TT ω.2) then 1 else 0)
          + N.fL0 (poolPos N x π cZ t (ω.1, padHist TT ω.2)))
        = ENNReal.ofReal γ * s0 t (Dm ω) + f0 t (Dm ω) := by
      intro ω t
      have h1 := ind_nonneg N.K0 hK0 (0 < π.order t ω.1 (padHist TT ω.2))
      rw [ENNReal.ofReal_add (by rw [mul_assoc]; exact mul_nonneg hγ0 h1) (hf0 _), mul_assoc,
        ENNReal.ofReal_mul hγ0]
    rw [lintegral_congr fun ω => Finset.sum_congr rfl fun t _ => hpt ω t,
      lintegral_finsetSum (f := fun t ω => ENNReal.ofReal γ * s0 t (Dm ω) + f0 t (Dm ω)) _
        fun t _ => (((hs0m t).comp hDmm).const_mul _).add ((hf0m t).comp hDmm),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lintegral_add_left (f := fun ω => ENNReal.ofReal γ * s0 t (Dm ω))
      (((hs0m t).comp hDmm).const_mul _),
      lintegral_const_mul (f := fun ω => s0 t (Dm ω)) _ ((hs0m t).comp hDmm)]
  -- (6) Lemma 1 for each retailer: `γ - 1` copies of `Fᵢ` with `γ Kᵢ / (γ - 1)` per dispatch
  have hret : ∀ i, ENNReal.ofReal (((T + N.L0 : ℕ) : ℝ) * Jr i)
      ≤ ∫⁻ ω, ∑ t ∈ Finset.range (T + N.L0), ENNReal.ofReal
        (γ * N.K i / (γ - 1) * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then 1 else 0)
          + N.F i (retPos N x π i t (ω.1, padHist TT ω.2))) ∂P
        + ENNReal.ofReal (γ * N.K i / (γ - 1)) := fun i =>
    sl_adapted_bound N.μ ν (fun a => a i) (measurable_pi_apply i)
      (fun t u d => π.dispatch t u d i) (fun t u d d' h => congrFun (hna t u d d' h).2 i)
      (fun t => hdis t i) (fun t u d => (hfeas u d t).2.1 i)
      (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s) (N.F i) (hFc i).measurable (hF0 i)
      (γ * N.K i / (γ - 1)) (Jr i) (vr i) (hvrm i) (hvrb i) (hvrs i) (T + N.L0) TT (by omega)
  have hSrT : ∀ i, ∫⁻ ω, ∑ t ∈ Finset.range (T + N.L0), ENNReal.ofReal
        (γ * N.K i / (γ - 1) * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then 1 else 0)
          + N.F i (retPos N x π i t (ω.1, padHist TT ω.2))) ∂P
      = ENNReal.ofReal (γ / (γ - 1)) * ∑ t ∈ Finset.range (T + N.L0), ∫⁻ ω, sr i t (Dm ω) ∂P
        + ∑ t ∈ Finset.range (T + N.L0), ∫⁻ ω, fr i t (Dm ω) ∂P := by
    intro i
    have hq0 : 0 ≤ γ / (γ - 1) := div_nonneg hγ0 hγ1.le
    have hpt : ∀ (ω : U × (Fin TT → DemandVec n)) (t : ℕ), ENNReal.ofReal
        (γ * N.K i / (γ - 1) * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then 1 else 0)
          + N.F i (retPos N x π i t (ω.1, padHist TT ω.2)))
        = ENNReal.ofReal (γ / (γ - 1)) * sr i t (Dm ω) + fr i t (Dm ω) := by
      intro ω t
      have h1 := ind_nonneg (N.K i) (hKi i) (0 < π.dispatch t ω.1 (padHist TT ω.2) i)
      have e : γ * N.K i / (γ - 1) * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then (1 : ℝ) else 0)
          = γ / (γ - 1) * (N.K i * (if 0 < π.dispatch t ω.1 (padHist TT ω.2) i then 1 else 0)) := by
        ring
      rw [e, ENNReal.ofReal_add (mul_nonneg hq0 h1) (hF0 i _), ENNReal.ofReal_mul hq0]
    rw [lintegral_congr fun ω => Finset.sum_congr rfl fun t _ => hpt ω t,
      lintegral_finsetSum (f := fun t ω => ENNReal.ofReal (γ / (γ - 1)) * sr i t (Dm ω)
        + fr i t (Dm ω)) _ fun t _ => (((hsrm i t).comp hDmm).const_mul _).add
          ((hfrm i t).comp hDmm),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (γ / (γ - 1)) * sr i t (Dm ω))
      (((hsrm i t).comp hDmm).const_mul _),
      lintegral_const_mul (f := fun ω => sr i t (Dm ω)) _ ((hsrm i t).comp hDmm)]
  -- (7) the pooled cost, over `T` periods, is at most warehouse plus retailer costs
  have hF0T : ∑ t ∈ Finset.range T, ∫⁻ ω, f0 t (Dm ω) ∂P
      ≤ ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, wc u (Dm ω) ∂P
        + ∑ i, ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, fr i u (Dm ω) ∂P := by
    calc ∑ t ∈ Finset.range T, ∫⁻ ω, f0 t (Dm ω) ∂P
        = ∑ t ∈ Finset.range T, ∫⁻ ω, e0 (t + N.L0) (Dm ω) ∂P :=
          Finset.sum_congr rfl fun t ht => hA4 t (Finset.mem_range.1 ht)
      _ ≤ ∑ t ∈ Finset.range T, (∫⁻ ω, wc (t + N.L0) (Dm ω) ∂P
            + ∑ i, ∫⁻ ω, fr i (t + N.L0) (Dm ω) ∂P) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [← lintegral_finsetSum (f := fun i ω => fr i (t + N.L0) (Dm ω)) _
              fun i _ => (hfrm i _).comp hDmm,
            ← lintegral_add_left (f := fun ω => wc (t + N.L0) (Dm ω)) ((hwcm _).comp hDmm)]
          exact lintegral_mono fun ω => hA5 _ _
      _ = ∑ t ∈ Finset.range T, ∫⁻ ω, wc (t + N.L0) (Dm ω) ∂P
            + ∑ i, ∑ t ∈ Finset.range T, ∫⁻ ω, fr i (t + N.L0) (Dm ω) ∂P := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ _ := add_le_add (sum_shift_le (fun u => ∫⁻ ω, wc u (Dm ω) ∂P) T N.L0 (T + N.L0) le_rfl)
          (Finset.sum_le_sum fun i _ =>
            sum_shift_le (fun u => ∫⁻ ω, fr i u (Dm ω) ∂P) T N.L0 (T + N.L0) le_rfl)
  have hFrT : ∀ i, ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, fr i u (Dm ω) ∂P
      ≤ ∑ t ∈ Finset.range TT, ∫⁻ ω, rr i t (Dm ω) ∂P := by
    intro i
    calc ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, fr i u (Dm ω) ∂P
        = ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, rr i (u + N.L i) (Dm ω) ∂P :=
          Finset.sum_congr rfl fun u hu => hA6 i u (Finset.mem_range.1 hu)
      _ ≤ _ := sum_shift_le (fun u => ∫⁻ ω, rr i u (Dm ω) ∂P) (T + N.L0) (N.L i) TT
          (by have := hLle i; omega)
  have hsub1 : ∀ (G : ℕ → ℝ≥0∞) (k : ℕ), k ≤ TT →
      ∑ t ∈ Finset.range k, G t ≤ ∑ t ∈ Finset.range TT, G t := fun G k hk =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hk)
  -- (8) assemble: `γ` copies of physical cost cover both lower bounds
  have h1γ : 1 + ENNReal.ofReal (γ - 1) = ENNReal.ofReal γ := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hγ1.le]
    congr 1
    ring
  have hγγ : ENNReal.ofReal (γ - 1) * ENNReal.ofReal (γ / (γ - 1)) = ENNReal.ofReal γ := by
    rw [← ENNReal.ofReal_mul hγ1.le]
    congr 1
    field_simp
  have hγ1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γ := ENNReal.one_le_ofReal.2 hγ.le
  set S0T := ∑ t ∈ Finset.range T, ∫⁻ ω, s0 t (Dm ω) ∂P with hS0Td
  set F0T := ∑ t ∈ Finset.range T, ∫⁻ ω, f0 t (Dm ω) ∂P with hF0Td
  set WT := ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, wc u (Dm ω) ∂P with hWTd
  set SrT := fun i => ∑ t ∈ Finset.range (T + N.L0), ∫⁻ ω, sr i t (Dm ω) ∂P with hSrTd
  set FrT := fun i => ∑ u ∈ Finset.range (T + N.L0), ∫⁻ ω, fr i u (Dm ω) ∂P with hFrTd
  set CK := ∑ i, ENNReal.ofReal (γ * N.K i / (γ - 1)) with hCK
  have hsum : ∑ i, ENNReal.ofReal (((T + N.L0 : ℕ) : ℝ) * Jr i)
      ≤ ENNReal.ofReal (γ / (γ - 1)) * ∑ i, SrT i + ∑ i, FrT i + CK := by
    calc ∑ i, ENNReal.ofReal (((T + N.L0 : ℕ) : ℝ) * Jr i)
        ≤ ∑ i, (ENNReal.ofReal (γ / (γ - 1)) * SrT i + FrT i
            + ENNReal.ofReal (γ * N.K i / (γ - 1))) :=
          Finset.sum_le_sum fun i _ => (hret i).trans (le_of_eq (by rw [hSrT i]))
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hA1]
  calc ENNReal.ofReal (T * J0)
        + ENNReal.ofReal (γ - 1) * ∑ i, ENNReal.ofReal (((T + N.L0 : ℕ) : ℝ) * Jr i)
      ≤ (ENNReal.ofReal γ * S0T + F0T + ENNReal.ofReal (γ * N.K0))
        + ENNReal.ofReal (γ - 1) * (ENNReal.ofReal (γ / (γ - 1)) * ∑ i, SrT i + ∑ i, FrT i + CK) := by
        gcongr
        exact hsup.trans (le_of_eq (by rw [hS0T]))
    _ ≤ (ENNReal.ofReal γ * S0T + (WT + ∑ i, FrT i) + ENNReal.ofReal (γ * N.K0))
        + ENNReal.ofReal (γ - 1) * (ENNReal.ofReal (γ / (γ - 1)) * ∑ i, SrT i + ∑ i, FrT i + CK) := by
        gcongr
    _ = ENNReal.ofReal γ * S0T + WT + (1 + ENNReal.ofReal (γ - 1)) * ∑ i, FrT i
        + (ENNReal.ofReal (γ - 1) * ENNReal.ofReal (γ / (γ - 1))) * ∑ i, SrT i
        + (ENNReal.ofReal (γ * N.K0) + ENNReal.ofReal (γ - 1) * CK) := by ring
    _ = ENNReal.ofReal γ * S0T + WT + ENNReal.ofReal γ * ∑ i, FrT i
        + ENNReal.ofReal γ * ∑ i, SrT i
        + (ENNReal.ofReal (γ * N.K0) + ENNReal.ofReal (γ - 1) * CK) := by rw [h1γ, hγγ]
    _ ≤ ENNReal.ofReal γ * ∑ t ∈ Finset.range TT, ∫⁻ ω, s0 t (Dm ω) ∂P
        + ENNReal.ofReal γ * ∑ t ∈ Finset.range TT, ∫⁻ ω, wc t (Dm ω) ∂P
        + ENNReal.ofReal γ * ∑ i, ∑ t ∈ Finset.range TT, ∫⁻ ω, rr i t (Dm ω) ∂P
        + ENNReal.ofReal γ * ∑ i, ∑ t ∈ Finset.range TT, ∫⁻ ω, sr i t (Dm ω) ∂P
        + (ENNReal.ofReal (γ * N.K0) + ENNReal.ofReal (γ - 1) * CK) := by
        gcongr
        · exact hsub1 _ T (by omega)
        · calc WT ≤ ∑ t ∈ Finset.range TT, ∫⁻ ω, wc t (Dm ω) ∂P := hsub1 _ _ (by omega)
            _ ≤ ENNReal.ofReal γ * ∑ t ∈ Finset.range TT, ∫⁻ ω, wc t (Dm ω) ∂P :=
              le_mul_of_one_le_left zero_le hγ1'
        · exact hFrT _
        · exact hsub1 _ _ (by omega)
    _ = _ := by ring

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

/-- With no retailers, aggregate demand is zero and the supplier value is `0`. -/
private lemma J0_zero_of_empty (N : Network 0) (k : ℝ) : N.J0 k = 0 := by
  have hagg : N.aggregate = Measure.dirac 0 := by
    unfold Network.aggregate
    have : (fun x : DemandVec 0 => ∑ i, x i) = fun _ => 0 := by
      funext x
      simp
    rw [this, Measure.map_const, measure_univ, one_smul]
  have hae : ∀ m : ℕ, ∀ᵐ z ∂(Measure.pi fun _ : Fin m => N.aggregate), ∀ j, z j = 0 := by
    intro m
    rw [hagg]
    refine ae_all_iff.2 fun j => ?_
    have h0 : ∀ᵐ a ∂(Measure.dirac (0 : ℝ≥0)), a = 0 :=
      (ae_dirac_iff (measurableSet_singleton (0 : ℝ≥0))).2 rfl
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => Measure.dirac (0 : ℝ≥0))
      (i := j)).eventually h0
  have hf0 : N.fL0 0 = 0 := by
    unfold Network.fL0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae N.L0] with z hz
    simp [hz, whLoss]
  refine le_antisymm ?_ zero_le
  have hadm : SLAdmissible (U := Unit) (fun _ _ _ => (0 : ℝ)) :=
    ⟨fun _ _ _ _ _ => rfl, fun _ => measurable_const, fun _ _ _ => le_rfl⟩
  unfold Network.J0 slValue
  refine iInf_le_of_le Unit (iInf_le_of_le inferInstance (iInf_le_of_le (Measure.dirac ())
    (iInf_le_of_le inferInstance (iInf_le_of_le (fun _ _ _ => (0 : ℝ))
      (iInf_le_of_le hadm ?_)))))
  unfold slAvgCost
  have hT : ∀ T : ℕ, ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (slPeriodCost N.fL0 k 0 (fun _ _ _ => (0 : ℝ)) ω.1 (padHist T ω.2) t)
        ∂((Measure.dirac ()).prod (Measure.pi fun _ : Fin T => N.aggregate)) = 0 := by
    intro T
    refine le_antisymm ?_ zero_le
    rw [Measure.dirac_prod]
    refine (lintegral_map_le _ _).trans ?_
    calc ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (slPeriodCost N.fL0 k 0 (fun _ _ _ => (0 : ℝ)) () (padHist T z) t)
            ∂(Measure.pi fun _ : Fin T => N.aggregate)
        ≤ ∫⁻ _z, 0 ∂(Measure.pi fun _ : Fin T => N.aggregate) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae T] with z hz
          have hpad : ∀ r, padHist T z r = 0 := by
            intro r
            unfold padHist
            split_ifs <;> simp [hz]
          refine le_of_eq (Finset.sum_eq_zero fun t _ => ?_)
          simp [slPeriodCost, slPos, hpad, hf0]
      _ = 0 := lintegral_zero
  simp only [hT, mul_zero, limsup_const, le_refl]

theorem solution {n : ℕ} (N : Network n) (hN : N.Standing)
    (hH : ∀ i, N.h ≤ N.H i) (x : InitState n) (hx : x.Valid) (γ : ℝ) (hγ : 1 < γ) :
    N.J0 (γ * N.K0) + ENNReal.ofReal (γ - 1) * ∑ i, N.J i (γ * N.K i / (γ - 1))
      ≤ ENNReal.ofReal γ * OPT N x := by
  have hγ0 : 0 ≤ γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  have hh : 0 < N.h := hN.h_pos
  have hp : 0 < N.p := hN.p_pos
  have hHi : ∀ i, 0 < N.H i := hN.H_pos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no retailers: the left side is `J₀(γ K₀) = 0`
    subst hn
    rw [J0_zero_of_empty N]
    simp
  -- the single-location data
  have hintM : ∀ i, Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) := fun i =>
    integrable_psum _ (integrable_marginal N hN i) _
  have hintA : Integrable (fun z : Fin N.L0 → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin N.L0 => N.aggregate) :=
    integrable_psum _ (integrable_aggregate N hN) _
  have hFnv : ∀ i, N.F i = nvCost (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
      (fun z => ∑ j, (z j : ℝ)) (N.H i) N.p := fun i => rfl
  have hfnv : N.fL0 = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate)
      (fun z => ∑ j, (z j : ℝ)) N.h N.p := by
    funext y
    unfold Network.fL0 nvCost whLoss
    congr 1
    funext z
    rw [neg_sub]
  have hX0 : ∀ (m : ℕ) (z : Fin m → ℝ≥0), 0 ≤ ∑ j, (z j : ℝ) := fun m z =>
    Finset.sum_nonneg fun j _ => (z j).2
  have hmsum : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hmargpos : ∀ i, 0 < ∫⁻ y, (y : ℝ≥0∞) ∂(N.marginal i) := fun i => by
    unfold Network.marginal
    rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  have haggpos : 0 < ∫⁻ y, (y : ℝ≥0∞) ∂N.aggregate := by
    unfold Network.aggregate
    rw [lintegral_map measurable_coe_nnreal_ennreal hmsum]
    have e : ∀ x : DemandVec n, ((∑ i, x i : ℝ≥0) : ℝ≥0∞) = ∑ i, ((x i : ℝ≥0) : ℝ≥0∞) := fun x => by
      push_cast
      rfl
    simp_rw [e]
    rw [lintegral_finsetSum _ fun i _ => (measurable_pi_apply i).coe_nnreal_ennreal]
    exact lt_of_lt_of_le (hN.mean_pos ⟨0, hn⟩)
      (Finset.single_le_sum (f := fun i => ∫⁻ x, ((x i : ℝ≥0) : ℝ≥0∞) ∂N.μ)
        (fun i _ => zero_le) (Finset.mem_univ _))
  -- Lemma 1 for the supplier problem and for every retailer problem
  obtain ⟨J0, hJ00, hJ0eq, v0, hv0m, hv0b, hv0s⟩ := sl_subsolution N.aggregate haggpos N.fL0
    (by rw [hfnv]; exact nv_continuous _ _ hintA _ _ hh.le hp.le)
    (by rw [hfnv]; exact nv_convex _ _ hintA _ _ hh.le hp.le)
    (fun y => by rw [hfnv]; exact nv_nonneg _ _ _ _ _ hh.le hp.le)
    (by rw [hfnv]; exact nv_coercive _ _ hintA _ _ hh hp)
    (by rw [hfnv]; exact nv_anti _ _ hintA (hX0 _) _ _ hp.le)
    (γ * N.K0) (mul_nonneg hγ0 hN.K0_nonneg)
  choose Jr hJr0 hJreq vr hvrm hvrb hvrs using fun i => sl_subsolution (N.marginal i) (hmargpos i)
    (N.F i) (by rw [hFnv i]; exact nv_continuous _ _ (hintM i) _ _ (hHi i).le hp.le)
    (F_properties N hN i).2.1 (F_properties N hN i).1
    (by rw [hFnv i]; exact nv_coercive _ _ (hintM i) _ _ (hHi i) hp)
    (by rw [hFnv i]; exact nv_anti _ _ (hintM i) (hX0 _) _ _ hp.le)
    (γ * N.K i / (γ - 1)) (div_nonneg (mul_nonneg hγ0 (hN.K_nonneg i)) hγ1.le)
  have hv0s' : ∀ y, J0 ≤ N.fL0 y + ∫ a, v0 (y - ((∑ i, a i : ℝ≥0) : ℝ)) ∂N.μ - v0 y := by
    intro y
    have h := hv0s y
    have e : ∫ d, v0 (y - (d : ℝ)) ∂N.aggregate = ∫ a, v0 (y - ((∑ i, a i : ℝ≥0) : ℝ)) ∂N.μ := by
      unfold Network.aggregate
      rw [integral_map (f := fun d : ℝ≥0 => v0 (y - (d : ℝ))) hmsum.aemeasurable
        (hv0m.comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable]
    rw [e] at h
    linarith [le_max_right (N.fL0 y - J0) 0]
  have hvrs' : ∀ i y, Jr i ≤ N.F i y + ∫ a, vr i (y - ((a i : ℝ≥0) : ℝ)) ∂N.μ - vr i y := by
    intro i y
    have h := hvrs i y
    have e : ∫ d, vr i (y - (d : ℝ)) ∂(N.marginal i)
        = ∫ a, vr i (y - ((a i : ℝ≥0) : ℝ)) ∂N.μ := by
      have hmi : Measurable fun a : DemandVec n => a i := measurable_pi_apply i
      unfold Network.marginal
      rw [integral_map (f := fun d : ℝ≥0 => vr i (y - (d : ℝ))) hmi.aemeasurable
        ((hvrm i).comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable]
    rw [e] at h
    linarith [le_max_right (N.F i y - Jr i) 0]
  -- the left side in closed form
  set Λ := J0 + (γ - 1) * ∑ i, Jr i with hΛ
  have hΛ0 : 0 ≤ Λ := add_nonneg hJ00 (mul_nonneg hγ1.le (Finset.sum_nonneg fun i _ => hJr0 i))
  have hLHS : N.J0 (γ * N.K0) + ENNReal.ofReal (γ - 1) * ∑ i, N.J i (γ * N.K i / (γ - 1))
      = ENNReal.ofReal Λ := by
    have e1 : N.J0 (γ * N.K0) = ENNReal.ofReal J0 := hJ0eq
    have e2 : ∀ i, N.J i (γ * N.K i / (γ - 1)) = ENNReal.ofReal (Jr i) := hJreq
    rw [e1, Finset.sum_congr rfl fun i _ => e2 i,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hJr0 i), ← ENNReal.ofReal_mul hγ1.le,
      ← ENNReal.ofReal_add hJ00 (mul_nonneg hγ1.le (Finset.sum_nonneg fun i _ => hJr0 i))]
  rw [hLHS]
  -- every admissible policy
  have hatop : ENNReal.ofReal γ ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : ENNReal.ofReal γ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  unfold OPT
  simp only [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine le_iInf fun U => le_iInf fun ms => le_iInf fun ν => le_iInf fun hν =>
    le_iInf fun π => le_iInf fun hπ => ?_
  set c := N.L0 + ∑ i, N.L i with hc
  set C := ENNReal.ofReal (γ * N.K0)
    + ENNReal.ofReal (γ - 1) * ∑ i, ENNReal.ofReal (γ * N.K i / (γ - 1)) with hC
  have hCtop : C ≠ ⊤ := by
    simp only [hC]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun i _ => ENNReal.ofReal_ne_top)⟩
  -- the finite-horizon bound at horizon `M = T + c`
  have hM : ∀ M : ℕ, c ≤ M →
      ENNReal.ofReal (((M - c : ℕ) : ℝ) * Λ) ≤ ENNReal.ofReal γ * expCost N x π ν M + C := by
    intro M hcM
    obtain ⟨T, rfl⟩ : ∃ T, M = T + c := ⟨M - c, by omega⟩
    have h := alloc_bound N hN hH x γ hγ ν π hπ J0 v0 hv0m hv0b hv0s' Jr vr hvrm hvrb hvrs' T
    have hTT : T + N.L0 + ∑ i, N.L i = T + c := by rw [hc]; ring
    rw [hTT] at h
    refine le_trans ?_ h
    rw [show T + c - c = T by omega, ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        mul_nonneg (Nat.cast_nonneg _) (hJr0 i)), ← ENNReal.ofReal_mul hγ1.le,
      ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hJ00)
        (mul_nonneg hγ1.le (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hJr0 i)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : ∀ i, (T : ℝ) * Jr i ≤ ((T + N.L0 : ℕ) : ℝ) * Jr i := fun i =>
      mul_le_mul_of_nonneg_right (by push_cast; linarith [(Nat.cast_nonneg N.L0 : (0 : ℝ) ≤ _)])
        (hJr0 i)
    have hs : (T : ℝ) * ∑ i, Jr i ≤ ∑ i, ((T + N.L0 : ℕ) : ℝ) * Jr i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hle i
    have := mul_le_mul_of_nonneg_left hs hγ1.le
    simp only [hΛ]
    nlinarith
  -- divide by the horizon and pass to the `limsup`
  unfold avgCost
  rw [← ENNReal.limsup_const_mul_of_ne_top hatop]
  have hC0 : Tendsto (fun M : ℕ => (M : ℝ≥0∞)⁻¹ * C) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hCtop)
    simpa using this
  have hlim : Tendsto (fun M : ℕ => (M : ℝ≥0∞)⁻¹ * ENNReal.ofReal (((M - c : ℕ) : ℝ) * Λ)) atTop
      (𝓝 (ENNReal.ofReal Λ)) := by
    have h1 : Tendsto (fun M : ℕ => ENNReal.ofReal (Λ - (c * Λ) / M)) atTop
        (𝓝 (ENNReal.ofReal Λ)) := by
      have := (tendsto_const_nhds (x := Λ)).sub (tendsto_const_div_atTop_nhds_zero_nat (c * Λ))
      rw [sub_zero] at this
      exact ENNReal.tendsto_ofReal this
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (c + 1)] with M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hdiv : (M : ℝ≥0∞)⁻¹ * ENNReal.ofReal (((M : ℝ) - (c : ℝ)) * Λ)
        = ENNReal.ofReal ((((M : ℝ) - (c : ℝ)) * Λ) / M) := by
      rw [ENNReal.ofReal_div_of_pos hMpos, ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
    rw [Nat.cast_sub (by omega), hdiv]
    congr 1
    field_simp
  calc ENNReal.ofReal Λ
      = limsup (fun M : ℕ => (M : ℝ≥0∞)⁻¹ * ENNReal.ofReal (((M - c : ℕ) : ℝ) * Λ)) atTop :=
        hlim.limsup_eq.symm
    _ ≤ limsup (fun M : ℕ => ENNReal.ofReal γ * ((M : ℝ≥0∞)⁻¹ * expCost N x π ν M)
          + (M : ℝ≥0∞)⁻¹ * C) atTop := by
        refine limsup_le_limsup (eventually_atTop.2 ⟨c, fun M hcM => ?_⟩)
        calc (M : ℝ≥0∞)⁻¹ * ENNReal.ofReal (((M - c : ℕ) : ℝ) * Λ)
            ≤ (M : ℝ≥0∞)⁻¹ * (ENNReal.ofReal γ * expCost N x π ν M + C) :=
              mul_le_mul_of_nonneg_left (hM M hcM) zero_le
          _ = ENNReal.ofReal γ * ((M : ℝ≥0∞)⁻¹ * expCost N x π ν M) + (M : ℝ≥0∞)⁻¹ * C := by
              ring
    _ ≤ limsup (fun M : ℕ => ENNReal.ofReal γ * ((M : ℝ≥0∞)⁻¹ * expCost N x π ν M)) atTop :=
        limsup_add_tendsto_zero _ _ hC0
