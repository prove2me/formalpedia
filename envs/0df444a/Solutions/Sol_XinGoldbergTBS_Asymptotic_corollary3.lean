-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.corollary3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T15:31:34.465405+00:00
-- url     : https://prove2.me/submissions/73fb9913-191e-4f25-bd4b-1d8e1f369b60

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness
import Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma4_opt_bound
import Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma4_bounds

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XGC3

open XinGoldbergTBS.Asymptotic

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

instance sumLaw_isProb (μ : DemandLaw) (L₀ : ℕ) : IsProbabilityMeasure (sumLaw μ L₀) := by
  unfold sumLaw; infer_instance

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

/-! ## Mixing a window of an i.i.d. path -/

def mix (m k : ℕ) (p y : Path) : Path := fun n => if m ≤ n ∧ n < m + k then y n else p n

lemma measurable_mix (m k : ℕ) : Measurable (fun q : Path × Path => mix m k q.1 q.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : m ≤ n ∧ n < m + k
  · simp only [mix, h, and_self, if_true]; fun_prop
  · simp only [mix, h, if_false]; fun_prop

lemma mp_mix (μ : DemandLaw) (m k : ℕ) :
    MeasurePreserving (fun q : Path × Path => mix m k q.1 q.2)
      ((pathLaw μ).prod (pathLaw μ)) (pathLaw μ) := by
  refine ⟨measurable_mix m k, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_mix m k) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun q : Path × Path => mix m k q.1 q.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi ↑(s.filter (fun i => ¬ (m ≤ i ∧ i < m + k))) t) ×ˢ
        (Set.pi ↑(s.filter (fun i => m ≤ i ∧ i < m + k)) t) := by
    ext ⟨p, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe, mix]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi,
        fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hw : m ≤ i ∧ i < m + k
      · simpa [hw] using h2 i ⟨hi, hw⟩
      · simpa [hw] using h1 i ⟨hi, hw⟩
  rw [hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht i), mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

/-- Reading finitely many distinct coordinates of an i.i.d. path gives the product law. -/
lemma mp_idx (μ : DemandLaw) (k : ℕ) (σ : Fin k → ℕ) (hσ : Function.Injective σ) :
    MeasurePreserving (fun p : Path => fun j : Fin k => p (σ j))
      (pathLaw μ) (Measure.pi fun _ : Fin k => μ.law) := by
  refine ⟨by fun_prop, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  set T : ℕ → Set ℝ := fun n => if h : ∃ j, σ j = n then s h.choose else Set.univ with hTdef
  have hT : ∀ j : Fin k, T (σ j) = s j := by
    intro j
    have hex : ∃ j', σ j' = σ j := ⟨j, rfl⟩
    simp only [hTdef, dif_pos hex]
    rw [hσ hex.choose_spec]
  have hpre : (fun p : Path => fun j : Fin k => p (σ j)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image σ) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hT]
    exact ⟨fun h a => h a (Set.mem_univ _), fun h a _ => h a⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n),
    Finset.prod_image (fun a _ b _ h => hσ h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma mp_window (μ : DemandLaw) (L₀ m : ℕ) :
    MeasurePreserving (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j))
      (pathLaw μ) (sumLaw μ L₀) :=
  mp_idx μ (L₀ + 1) (fun j => m + j) (fun a b h => Fin.ext (by simpa using h))

lemma lintegral_mix_path (μ : DemandLaw) (m k : ℕ) {f : Path → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ d, f d ∂pathLaw μ = ∫⁻ d, ∫⁻ y, f (mix m k d y) ∂pathLaw μ ∂pathLaw μ := by
  rw [← (mp_mix μ m k).lintegral_comp hf]
  exact lintegral_prod (fun q : Path × Path => f (mix m k q.1 q.2))
    (hf.comp (measurable_mix m k)).aemeasurable

/-! ## Running maxima and reversal -/

def Zb (r : ℝ) (d : Path) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (Zb r d n) (W r d (n + 1))

def sh (d : Path) : Path := fun n => d (n + 1)

lemma W_succ (r : ℝ) (d : Path) (k : ℕ) : W r d (k + 1) = (r - d 0) + W r (sh d) k := by
  unfold W sh; rw [Finset.sum_range_succ']; ring

lemma W_zero (r : ℝ) (d : Path) : W r d 0 = 0 := by simp [W]

lemma Zb_front (r : ℝ) (d : Path) (n : ℕ) :
    Zb r d (n + 1) = max 0 ((r - d 0) + Zb r (sh d) n) := by
  induction n with
  | zero => simp [Zb, W_succ, W_zero]
  | succ n ih =>
    rw [Zb, ih, W_succ, Zb, max_assoc, ← max_add_add_left]

lemma Zb_mono (r : ℝ) (d : Path) : Monotone (fun n => Zb r d n) :=
  monotone_nat_of_le_succ fun n => le_max_left _ _

lemma W_le_Zb (r : ℝ) (d : Path) (n : ℕ) : W r d n ≤ Zb r d n := by
  cases n with
  | zero => simp [Zb, W_zero]
  | succ n => exact le_max_right _ _

lemma Zb_local (r : ℝ) (d d' : Path) (n : ℕ) (h : ∀ j < n, d j = d' j) : Zb r d n = Zb r d' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Zb]
    rw [ih fun j hj => h j (by omega)]
    congr 1
    unfold W
    exact Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]

lemma measurable_W' (r : ℝ) (i : ℕ) : Measurable (fun d : Path => W r d i) := by
  unfold W; fun_prop

lemma measurable_Zb (r : ℝ) (n : ℕ) : Measurable (fun d : Path => Zb r d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_W' r (n + 1))

lemma Z_eq_Zb (r : ℝ) (d : Path) (n : ℕ) : Z r d (n + 1) = Zb r d n := by
  apply le_antisymm
  · unfold Z
    exact ciSup_le fun i => (W_le_Zb r d i).trans (Zb_mono r d (by omega : (i : ℕ) ≤ n))
  · obtain ⟨j, hj, hjeq⟩ : ∃ j ≤ n, Zb r d n = W r d j := by
      induction n with
      | zero => exact ⟨0, le_rfl, by simp [Zb, W_zero]⟩
      | succ n ih =>
        obtain ⟨j, hj, he⟩ := ih
        rcases le_total (Zb r d n) (W r d (n + 1)) with h | h
        · exact ⟨n + 1, le_rfl, by simp only [Zb]; rw [max_eq_right h]⟩
        · exact ⟨j, by omega, by simp only [Zb]; rw [max_eq_left h, he]⟩
    rw [hjeq]; unfold Z
    exact le_ciSup (Set.finite_range (fun i : Fin (n + 1) => W r d i)).bddAbove
      (⟨j, by omega⟩ : Fin (n + 1))

def pad (n : ℕ) (z : Fin n → ℝ) : Path := fun l => if h : l < n then z ⟨l, h⟩ else 0

lemma measurable_pad (n : ℕ) : Measurable (pad n) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h : l < n
  · simp only [pad, h, dif_pos]; exact measurable_pi_apply _
  · simp only [pad, h, dif_neg, not_false_eq_true]; exact measurable_const

/-- Lindley recursion (backward running maximum of the increments `r - D`). -/
def R (r : ℝ) (d : Path) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max 0 (R r d n + (r - d n))

lemma measurable_R (r : ℝ) (n : ℕ) : Measurable (fun d : Path => R r d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable (fun d : Path => max 0 (R r d n + (r - d n)))
    exact measurable_const.max (ih.add (measurable_const.sub (measurable_pi_apply n)))

lemma R_local (r : ℝ) (d d' : Path) (n : ℕ) (h : ∀ j < n, d j = d' j) : R r d n = R r d' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [R]
    rw [ih fun j hj => h j (by omega), h n (by omega)]

lemma R_eq (r : ℝ) (d : Path) (n : ℕ) :
    R r d n = Zb r (pad n (fun j : Fin n => d (n - 1 - j))) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [R, Zb_front, ih]
    have h0 : pad (n + 1) (fun j : Fin (n + 1) => d (n + 1 - 1 - j)) 0 = d n := by
      simp only [pad, dif_pos (Nat.succ_pos n)]
      congr 1
    have hs : sh (pad (n + 1) (fun j : Fin (n + 1) => d (n + 1 - 1 - j))) =
        pad n (fun j : Fin n => d (n - 1 - j)) := by
      funext l
      simp only [sh, pad]
      by_cases hl : l < n
      · rw [dif_pos (by omega), dif_pos hl]
        show d (n + 1 - 1 - (l + 1)) = d (n - 1 - l)
        rw [show n + 1 - 1 - (l + 1) = n - 1 - l by omega]
      · rw [dif_neg (by omega), dif_neg hl]
    rw [h0, hs, add_comm (Zb _ _ _)]

lemma transfer (μ : DemandLaw) (n : ℕ) (σ : Fin n → ℕ) (hσ : Function.Injective σ)
    (g : Path → ℝ≥0∞) (hg : Measurable g)
    (hloc : ∀ d d' : Path, (∀ j < n, d j = d' j) → g d = g d') :
    ∫⁻ d, g (pad n (fun j => d (σ j))) ∂pathLaw μ = ∫⁻ d, g d ∂pathLaw μ := by
  have h1 := (mp_idx μ n σ hσ).lintegral_comp (hg.comp (measurable_pad n))
  have h2 := (mp_idx μ n (fun j => (j : ℕ)) (fun a b h => Fin.ext h)).lintegral_comp
    (hg.comp (measurable_pad n))
  simp only [Function.comp] at h1 h2
  rw [h1, ← h2]
  refine lintegral_congr fun d => hloc _ _ fun j hj => ?_
  simp [pad, hj]

lemma E_R (μ : DemandLaw) (r : ℝ) (n : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ d, f (R r d n) ∂pathLaw μ = ∫⁻ d, f (Zb r d n) ∂pathLaw μ := by
  simp only [R_eq]
  exact transfer μ n (fun j => n - 1 - j) (fun a b h => by
      have := a.isLt; have := b.isLt; exact Fin.ext (by simp only at h; omega))
    (fun d => f (Zb r d n)) (hf.comp (measurable_Zb r n))
    (fun d d' h => by rw [Zb_local r d d' n h])

/-! ## The base-stock policy -/

lemma upTo_eq (π : SSPolicy) (r S : ℝ) (hπ : IsStationaryMarkov π (baseStockRule S) r S)
    (d : Path) (n : ℕ) : ssOrderUpTo π r S d n = S + R r d n := by
  have key : ∀ m, ssOrderUpTo π r S d m = max (ssPosition π r S d m) S := by
    intro m
    simp only [ssOrderUpTo, hπ.2 m d, baseStockRule, Real.coe_toNNReal']
    rcases le_total (ssPosition π r S d m) S with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]; ring
    · rw [max_eq_right (by linarith), max_eq_left h]; ring
  induction n with
  | zero => rw [key]; simp [ssPosition, R]
  | succ n ih =>
    have e : ssPosition π r S d (n + 1) = ssOrderUpTo π r S d n - (d n - r) := rfl
    rw [key, e, ih, R]
    rcases le_total 0 (R r d n + (r - d n)) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma measurable_cost (κ : Costs) (L₀ : ℕ) (r S : ℝ) (n : ℕ) :
    Measurable (fun d : Path => ENNReal.ofReal
      (G κ (S + R r d n - ∑ k ∈ Finset.range (L₀ + 1), (d (n + k) - r)))) :=
  ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
    ((measurable_const.add (measurable_R r n)).sub
      (Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).sub measurable_const)))

lemma E_cost (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r S : ℝ) (n : ℕ) :
    ∫⁻ d, ENNReal.ofReal (G κ (S + R r d n - ∑ k ∈ Finset.range (L₀ + 1), (d (n + k) - r)))
        ∂pathLaw μ =
      ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
        ENNReal.ofReal (G κ (S + Z r p.1 (n + 1) - ∑ i, (p.2 i - r)))
        ∂((pathLaw μ).prod (sumLaw μ L₀)) := by
  set h : ℝ → ℝ≥0∞ := fun z =>
    ∫⁻ w, ENNReal.ofReal (G κ (S + z - ∑ i, (w i - r))) ∂sumLaw μ L₀ with hh
  have hF : Measurable (fun q : ℝ × (Fin (L₀ + 1) → ℝ) =>
      ENNReal.ofReal (G κ (S + q.1 - ∑ i, (q.2 i - r)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp (by fun_prop))
  have hhm : Measurable h := hF.lintegral_prod_right'
  have hR : ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
        ENNReal.ofReal (G κ (S + Z r p.1 (n + 1) - ∑ i, (p.2 i - r)))
        ∂((pathLaw μ).prod (sumLaw μ L₀)) = ∫⁻ d, h (Zb r d n) ∂pathLaw μ := by
    have hm : Measurable (fun p : Path × (Fin (L₀ + 1) → ℝ) =>
        ENNReal.ofReal (G κ (S + Z r p.1 (n + 1) - ∑ i, (p.2 i - r)))) := by
      have : (fun p : Path × (Fin (L₀ + 1) → ℝ) =>
          ENNReal.ofReal (G κ (S + Z r p.1 (n + 1) - ∑ i, (p.2 i - r)))) =
          (fun q : ℝ × (Fin (L₀ + 1) → ℝ) => ENNReal.ofReal (G κ (S + q.1 - ∑ i, (q.2 i - r)))) ∘
            (fun p : Path × (Fin (L₀ + 1) → ℝ) => (Zb r p.1 n, p.2)) := by
        funext p; simp only [Function.comp, Z_eq_Zb]
      rw [this]
      exact hF.comp (((measurable_Zb r n).comp measurable_fst).prodMk measurable_snd)
    rw [lintegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun d => ?_
    simp only [hh, Z_eq_Zb]
  have hL : ∫⁻ d, ENNReal.ofReal (G κ (S + R r d n - ∑ k ∈ Finset.range (L₀ + 1), (d (n + k) - r)))
        ∂pathLaw μ = ∫⁻ d, h (R r d n) ∂pathLaw μ := by
    rw [lintegral_mix_path μ n (L₀ + 1) (measurable_cost κ L₀ r S n)]
    refine lintegral_congr fun d => ?_
    have hRl : ∀ y, R r (mix n (L₀ + 1) d y) n = R r d n := fun y =>
      R_local r _ _ n fun j hj => by simp only [mix]; rw [if_neg (by omega)]
    have hw : ∀ y : Path, ∑ k ∈ Finset.range (L₀ + 1), (mix n (L₀ + 1) d y (n + k) - r) =
        ∑ i : Fin (L₀ + 1), ((fun j : Fin (L₀ + 1) => y (n + j)) i - r) := by
      intro y
      rw [Finset.sum_range (fun k => mix n (L₀ + 1) d y (n + k) - r)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := k.isLt
      simp only [mix]; rw [if_pos (by omega)]
    simp only [hRl, hw]
    have hcomp := (mp_window μ L₀ n).lintegral_comp
      (f := fun w : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (S + R r d n - ∑ i, (w i - r))))
      (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
        (measurable_const.sub (by fun_prop))))
    simp only at hcomp
    rw [hcomp]
  rw [hL, hR]
  exact E_R μ r n h hhm

/-- The discounted cost of the base-stock policy at level `S`, started at `x = S`. -/
theorem disc_eq (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r S : ℝ) (π : SSPolicy)
    (hπ : IsStationaryMarkov π (baseStockRule S) r S) :
    ∫⁻ d, ssDiscCost κ L₀ α π r S d ∂pathLaw μ =
      ∑' k : ℕ, ENNReal.ofReal (α ^ k) *
        ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          ENNReal.ofReal (G κ (S + Z r p.1 (k + 1) - ∑ i, (p.2 i - r)))
          ∂((pathLaw μ).prod (sumLaw μ L₀)) := by
  have hpt : ∀ d i, ssCost κ L₀ π r S d i = ENNReal.ofReal
      (G κ (S + R r d i - ∑ k ∈ Finset.range (L₀ + 1), (d (i + k) - r))) := by
    intro d i; simp only [ssCost, upTo_eq π r S hπ d i]
  simp only [ssDiscCost, hpt]
  rw [lintegral_tsum (f := fun i (d : Path) => ENNReal.ofReal (α ^ i) * ENNReal.ofReal
      (G κ (S + R r d i - ∑ k ∈ Finset.range (L₀ + 1), (d (i + k) - r))))
    (fun i => (measurable_const.mul (measurable_cost κ L₀ r S i)).aemeasurable)]
  refine tsum_congr fun i => ?_
  rw [lintegral_const_mul _ (measurable_cost κ L₀ r S i), E_cost]

end XGC3

open MeasureTheory ProbabilityTheory Filter XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          ∑' k : ℕ, ENNReal.ofReal (α ^ k) *
            ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
              ENNReal.ofReal (G κ (Sinf μ κ L₀ α (rL P L₀ L χ) + Z (rL P L₀ L χ) p.1 (k + 1)
                - ∑ i, (p.2 i - rL P L₀ L χ)))
              ∂((pathLaw μ).prod (sumLaw μ L₀))
      ≤ OPT μ κ L₀ L +
        ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by
  obtain ⟨π, hπ, hcost⟩ :=
    ((lemma4_bounds μ κ L₀ α hα0 hα1).2.2 (rL P L₀ L χ)).2.2.2.2.2.2 (Sinf μ κ L₀ α (rL P L₀ L χ))
  rw [← XGC3.disc_eq μ κ L₀ α (rL P L₀ L χ) (Sinf μ κ L₀ α (rL P L₀ L χ)) π hπ, hcost]
  exact lemma4_opt_bound μ κ L₀ L hL P χ q I D hw α hα0 hα1
