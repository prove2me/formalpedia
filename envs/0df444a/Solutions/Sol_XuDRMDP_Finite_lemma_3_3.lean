-- Prove2me | solution 1 for XuDRMDP.Finite.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:54:05.688357+00:00
-- url     : https://prove2.me/submissions/f2da49ff-092d-4cb9-9df0-6f9bece08b9e

import Mathlib
import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
open MeasureTheory

namespace S227Xu

noncomputable def D {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) : ℝ :=
  c i - if h : i.val = 0 then 0 else c ⟨i.val - 1, by omega⟩

def fN {α : Type*} {L : ℕ} (c : Fin (L+1) → α) (k : ℕ) : α := c ⟨min k L, by omega⟩

noncomputable def dN {L : ℕ} (c : Fin (L+1) → ℝ) (k : ℕ) : ℝ :=
  fN c k - if k = 0 then 0 else fN c (k-1)

lemma fN_fin {α : Type*} {L : ℕ} (c : Fin (L+1) → α) (i : Fin (L+1)) : fN c i = c i := by
  unfold fN; congr 1; ext; simp; omega

lemma D_eq {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) : D c i = dN c i := by
  unfold D dN
  rw [fN_fin]
  by_cases h : i.val = 0
  · simp [h]
  · simp only [h, dite_false, if_false]
    unfold fN; congr 2; ext; simp

lemma sum_dN {L : ℕ} (c : Fin (L+1) → ℝ) (i : ℕ) :
    ∑ k ∈ Finset.range (i+1), dN c k = fN c i := by
  induction i with
  | zero => simp [dN]
  | succ i ih => rw [Finset.sum_range_succ, ih]; simp [dN]

lemma D_nonneg {L : ℕ} {c : Fin (L+1) → ℝ} (h0 : ∀ i, 0 ≤ c i) (hm : Monotone c)
    (i : Fin (L+1)) : 0 ≤ D c i := by
  unfold D
  split_ifs with h
  · simpa using h0 i
  · have : c ⟨i.val - 1, by omega⟩ ≤ c i := hm (by rw [Fin.le_iff_val_le_val]; simp)
    linarith

lemma partial_sum {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) :
    ∑ j, (if j ≤ i then D c j else 0) = c i := by
  have h1 : ∑ j : Fin (L+1), (if j ≤ i then D c j else 0) =
      ∑ j : Fin (L+1), (fun k : ℕ => if k ≤ i.val then dN c k else 0) j.val := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.le_iff_val_le_val, D_eq]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k ≤ i.val then dN c k else 0) (L+1), ← Finset.sum_range_add_sum_Ico _ (show i.val + 1 ≤ L + 1 by omega)]
  have h2 : ∑ k ∈ Finset.Ico (i.val+1) (L+1), (if k ≤ i.val then dN c k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk => by simp at hk; simp; omega
  have h3 : ∑ k ∈ Finset.range (i.val+1), (if k ≤ i.val then dN c k else 0) =
      ∑ k ∈ Finset.range (i.val+1), dN c k :=
    Finset.sum_congr rfl fun k hk => by simp at hk; simp; omega
  rw [h2, h3, sum_dN, fN_fin, add_zero]

lemma total_sum {L : ℕ} (c : Fin (L+1) → ℝ) : ∑ j, D c j = c (Fin.last L) := by
  rw [← partial_sum c (Fin.last L)]
  exact Finset.sum_congr rfl fun j _ => by simp [Fin.le_last]

lemma abel (f m : ℕ → ℝ) (L : ℕ) :
    ∑ k ∈ Finset.range (L+1), (f k - if k = 0 then 0 else f (k-1)) * m k =
      f L * m L - ∑ k ∈ Finset.range L, f k * (m (k+1) - m k) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => f k * (m (k+1) - m k))]
    simp; ring

/-- The bound in Abel form. -/
lemma abel_bound {L : ℕ} (c : Fin (L+1) → ℝ) (hl : c (Fin.last L) = 1) (M : Fin (L+1) → ℝ) :
    fN M 0 + ∑ k ∈ Finset.range L, (fN M (k+1) - fN M k) * (1 - fN c k) =
      ∑ i, D c i * M i := by
  have h1 : ∑ i, D c i * M i = ∑ i : Fin (L+1), (fun k : ℕ => dN c k * fN M k) i.val :=
    Finset.sum_congr rfl fun i _ => by simp only [D_eq, fN_fin]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => dN c k * fN M k) (L+1)]
  unfold dN
  rw [abel]
  have hL : fN c L = 1 := by rw [← hl]; unfold fN; congr; simp
  have := Finset.sum_range_sub (fN M) L
  rw [hL]
  have e : ∑ k ∈ Finset.range L, (fN M (k+1) - fN M k) * (1 - fN c k) =
      ∑ k ∈ Finset.range L, (fN M (k+1) - fN M k) - ∑ k ∈ Finset.range L, fN c k * (fN M (k+1) - fN M k) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, this]; ring

lemma fN_mono {α : Type*} [Preorder α] {L : ℕ} {c : Fin (L+1) → α} (h : Monotone c) :
    Monotone (fN c) := fun k k' hk => h (by rw [Fin.le_iff_val_le_val]; simp; omega)

lemma fN_last {α : Type*} {L : ℕ} (c : Fin (L+1) → α) : fN c L = c (Fin.last L) := by
  unfold fN; congr; simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma sup_dir {L : ℕ} {c : Fin (L+1) → ℝ} (h0 : ∀ i, 0 ≤ c i) (hm : Monotone c)
    (hl : c (Fin.last L) = 1) {S : Fin (L+1) → Set E} (hnest : Monotone S)
    (y : Fin (L+1) → E) (hy : ∀ i, y i ∈ S i) :
    ∃ μ : Measure E, (IsProbabilityMeasure μ ∧ μ (S (Fin.last L)) = 1 ∧
      ∀ i, ENNReal.ofReal (c i) ≤ μ (S i)) ∧ ∫ x, x ∂μ = ∑ i, D c i • y i := by
  have hD := D_nonneg h0 hm
  set μ : Measure E := ∑ i, ENNReal.ofReal (D c i) • Measure.dirac (y i) with hμ
  have happ : ∀ A, μ A = ∑ i, ENNReal.ofReal (D c i) * A.indicator 1 (y i) := by
    intro A; simp [μ, Measure.dirac_apply]
  have htot : ∑ i, ENNReal.ofReal (D c i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hD i), total_sum, hl, ENNReal.ofReal_one]
  have hall : ∀ A, (∀ i, y i ∈ A) → μ A = 1 := by
    intro A hA; rw [happ, ← htot]
    exact Finset.sum_congr rfl fun i _ => by simp [Set.indicator_of_mem (hA i)]
  refine ⟨μ, ⟨⟨hall _ fun i => Set.mem_univ _⟩,
    hall _ fun i => hnest (Fin.le_last i) (hy i), fun i => ?_⟩, ?_⟩
  · rw [happ, ← partial_sum c i, ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> simp [hD])]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · simp [Set.indicator_of_mem (hnest h (hy j))]
    · simp
  · rw [hμ, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hD i)]
    · intro i _
      exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

lemma ptwise {L : ℕ} (ℓ : E →L[ℝ] ℝ) {S : Fin (L+1) → Set E} (hnest : Monotone S)
    {M : Fin (L+1) → ℝ} (hMm : Monotone M) (hM : ∀ i, ∀ z ∈ S i, ℓ z ≤ M i) :
    ∀ J, ∀ x ∈ fN S J, ℓ x ≤ fN M 0 +
      ∑ k ∈ Finset.range J, (fN M (k+1) - fN M k) * (fN S k)ᶜ.indicator (fun _ => (1:ℝ)) x := by
  have hM' : ∀ k, ∀ z ∈ fN S k, ℓ z ≤ fN M k := fun k => hM _
  intro J
  induction J with
  | zero => intro x hx; simpa using hM' 0 x hx
  | succ J ih =>
    intro x hx
    by_cases hxJ : x ∈ fN S J
    · rw [Finset.sum_range_succ]
      have h1 := ih x hxJ
      have h2 : 0 ≤ (fN M (J+1) - fN M J) * (fN S J)ᶜ.indicator (fun _ => (1:ℝ)) x :=
        mul_nonneg (sub_nonneg.2 (fN_mono hMm (Nat.le_succ J)))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
    · have e : ∑ k ∈ Finset.range (J+1), (fN M (k+1) - fN M k) *
          (fN S k)ᶜ.indicator (fun _ => (1:ℝ)) x =
          ∑ k ∈ Finset.range (J+1), (fN M (k+1) - fN M k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : x ∈ (fN S k)ᶜ := fun h => hxJ (fN_mono hnest
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h)
        rw [Set.indicator_of_mem this, mul_one]
      rw [e, Finset.sum_range_sub]
      have := hM' (J+1) x hx
      linarith

lemma sub_dir {L : ℕ} {c : Fin (L+1) → ℝ} (hl : c (Fin.last L) = 1)
    {S : Fin (L+1) → Set E} (hne : ∀ i, (S i).Nonempty) (hconv : ∀ i, Convex ℝ (S i))
    (hcomp : ∀ i, IsCompact (S i)) (hnest : Monotone S)
    (μ : Measure E) [IsProbabilityMeasure μ] (hL : μ (S (Fin.last L)) = 1)
    (hc : ∀ i, ENNReal.ofReal (c i) ≤ μ (S i)) :
    ∃ y : Fin (L+1) → E, (∀ i, y i ∈ S i) ∧ ∫ x, x ∂μ = ∑ i, D c i • y i := by
  set R : Set E := {x | ∃ y : Fin (L+1) → E, (∀ i, y i ∈ S i) ∧ x = ∑ i, D c i • y i} with hR
  have hRi : R = (fun y : Fin (L+1) → E => ∑ i, D c i • y i) '' Set.univ.pi S := by
    ext x; simp [R, eq_comm]
  have hRc : IsCompact R := by
    rw [hRi]; exact (isCompact_univ_pi hcomp).image (by fun_prop)
  have hRconv : Convex ℝ R := by
    rw [hRi]
    refine Convex.is_linear_image (convex_pi fun i _ => hconv i) ?_
    constructor
    · intro y z; simp [Finset.sum_add_distrib, smul_add]
    · intro r y; simp [Finset.smul_sum, smul_comm r]
  suffices h : ∫ x, x ∂μ ∈ R by
    obtain ⟨y, hy, e⟩ := h; exact ⟨y, hy, e⟩
  by_contra hm
  obtain ⟨ℓ, u, hlt, hu⟩ := geometric_hahn_banach_closed_point hRconv hRc.isClosed hm
  choose ym hym hmax using fun i => (hcomp i).exists_isMaxOn (hne i) ℓ.continuous.continuousOn
  set M : Fin (L+1) → ℝ := fun i => ℓ (ym i) with hMdef
  have hM : ∀ i, ∀ z ∈ S i, ℓ z ≤ M i := fun i z hz => hmax i hz
  have hMm : Monotone M := fun i j h => hM j _ (hnest h (hym i))
  have hr : ℓ (∑ i, D c i • ym i) < u := hlt _ ⟨ym, hym, rfl⟩
  rw [map_sum] at hr
  simp only [map_smul, smul_eq_mul] at hr
  -- integrability
  have hmeas : ∀ i, MeasurableSet (S i) := fun i => (hcomp i).isClosed.measurableSet
  have hcompl : μ (S (Fin.last L))ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (hmeas _), hL]; simp
  have hae : ∀ᵐ x ∂μ, x ∈ S (Fin.last L) := mem_ae_iff.2 hcompl
  have hint : Integrable (fun x : E => x) μ := by
    have := (continuous_id.continuousOn (s := S (Fin.last L))).integrableOn_compact
      (μ := μ) (hcomp _)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  rw [← ℓ.integral_comp_comm hint] at hu
  set g : E → ℝ := fun x => fN M 0 +
      ∑ k ∈ Finset.range L, (fN M (k+1) - fN M k) * (fN S k)ᶜ.indicator (fun _ => (1:ℝ)) x
    with hg
  have hmeasN : ∀ k, MeasurableSet (fN S k) := fun k => hmeas _
  have hgint : Integrable g μ :=
    (integrable_const _).add (integrable_finsetSum _ fun k _ =>
      ((integrable_const (1:ℝ)).indicator (hmeasN k).compl).const_mul _)
  have hle : ∫ x, ℓ x ∂μ ≤ ∫ x, g x ∂μ := by
    refine integral_mono_ae (ℓ.integrable_comp hint) hgint ?_
    filter_upwards [hae] with x hx
    exact ptwise ℓ hnest hMm hM L x (by rwa [fN_last])
  have hgval : ∫ x, g x ∂μ = fN M 0 +
      ∑ k ∈ Finset.range L, (fN M (k+1) - fN M k) * (1 - μ.real (fN S k)) := by
    rw [hg, integral_add (integrable_const _) (integrable_finsetSum _ fun k _ =>
      ((integrable_const (1:ℝ)).indicator (hmeasN k).compl).const_mul _),
      integral_finsetSum _ fun k _ =>
      ((integrable_const (1:ℝ)).indicator (hmeasN k).compl).const_mul _]
    simp only [integral_const, integral_const_mul, integral_indicator_const _ (hmeasN _).compl,
      measureReal_compl (hmeasN _), probReal_univ, smul_eq_mul, mul_one, one_mul]
  have hbound : ∫ x, g x ∂μ ≤ ∑ i, D c i * M i := by
    rw [hgval, ← abel_bound c hl M]
    gcongr with k hk
    · exact sub_nonneg.2 (fN_mono hMm (Nat.le_succ k))
    · unfold fN
      have := hc ⟨min k L, by omega⟩
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)] at this
      exact this
  linarith

end S227Xu

open XuDRMDP.Finite in
theorem solution {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (s : Fin n) :
    {x | ∃ μ ∈ localClass U s, localMean μ = x} = reducedSet U s := by
  ext x
  constructor
  · rintro ⟨μ, ⟨hp, hL, hc⟩, rfl⟩
    exact S227Xu.sub_dir U.confidence_last (U.nonempty s) (U.convex s) (U.compact s)
      (U.nested s) μ hL hc
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨μ, hμ, he⟩ := S227Xu.sup_dir U.confidence_nonneg U.confidence_mono
      U.confidence_last (U.nested s) y hy
    exact ⟨μ, hμ, he⟩
