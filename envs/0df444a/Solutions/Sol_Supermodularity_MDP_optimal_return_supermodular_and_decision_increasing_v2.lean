-- Prove2me | solution 1 for Supermodularity.MDP.optimal_return_supermodular_and_decision_increasing_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T18:02:17.586396+00:00
-- url     : https://prove2.me/submissions/97bb4e7f-c1b5-4b2f-b047-0a902f6160c9

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

set_option autoImplicit false

open MeasureTheory

namespace P03c74cda

open Set

variable {α : Type*} [MeasurableSpace α] [Preorder α]

lemma meas_eq_upper (ν : Measure α) (T : Set α) (hT : ν Tᶜ = 0) (A : Set α)
    (hA : ∀ a ∈ A ∩ T, ∀ b ∈ T, a ≤ b → b ∈ A) :
    ν A = ν ((upperClosure (A ∩ T) : Set α)) := by
  rw [← measure_inter_conull (s := A) hT,
    ← measure_inter_conull (s := ((upperClosure (A ∩ T) : UpperSet α) : Set α)) hT]
  congr 1
  ext w
  simp only [mem_inter_iff, SetLike.mem_coe, mem_upperClosure]
  constructor
  · rintro ⟨hwA, hwT⟩
    exact ⟨⟨w, ⟨hwA, hwT⟩, le_rfl⟩, hwT⟩
  · rintro ⟨⟨a, haAT, haw⟩, hwT⟩
    exact ⟨hA a haAT w hwT haw, hwT⟩

lemma real_to_ennreal_ineq {a b c d : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (h : a.toReal + b.toReal ≤ c.toReal + d.toReal) : a + b ≤ c + d := by
  rw [← ENNReal.toReal_add ha hb, ← ENNReal.toReal_add hc hd] at h
  exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨ha, hb⟩)
    (ENNReal.add_ne_top.2 ⟨hc, hd⟩)).1 h

lemma ennreal_to_real_ineq {a b c d : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (h : a + b ≤ c + d) : a.toReal + b.toReal ≤ c.toReal + d.toReal := by
  rw [← ENNReal.toReal_add ha hb, ← ENNReal.toReal_add hc hd]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hc, hd⟩) h

lemma pos_layer (ν : Measure α) (h : α → ℝ) (hm : AEMeasurable h ν) :
    ∫⁻ w, ENNReal.ofReal (h w) ∂ν = ∫⁻ t in Ioi 0, ν {w | t < h w} := by
  have e1 := lintegral_eq_lintegral_meas_lt ν (f := fun w => max (h w) 0)
    (Filter.Eventually.of_forall fun w => le_max_right _ _) (hm.max aemeasurable_const)
  have e2 : (fun w => ENNReal.ofReal (max (h w) 0)) = fun w => ENNReal.ofReal (h w) := by
    funext w
    rcases le_total (h w) 0 with hw | hw
    · rw [max_eq_right hw, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hw]
    · rw [max_eq_left hw]
  rw [e2] at e1
  rw [e1]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have e : {a | t < max (h a) 0} = {a | t < h a} := by
    ext w
    simp only [mem_setOf_eq, lt_max_iff]
    constructor
    · rintro (h1 | h1)
      · exact h1
      · exact absurd h1 (lt_asymm (mem_Ioi.1 ht))
    · exact Or.inl
  simp only [e]

lemma anti_meas (ν : Measure α) (h : α → ℝ) : Measurable fun t : ℝ => ν {w | t < h w} :=
  Antitone.measurable (fun s t hst => measure_mono fun w (hw : t < h w) => lt_of_le_of_lt hst hw)

lemma compl_toReal (ν : Measure α) (hν : IsProbabilityMeasure ν) (h : α → ℝ)
    (hm : AEMeasurable h ν) (c : ℝ) :
    (ν {w | h w < c}).toReal = 1 - (ν {w | c ≤ h w}).toReal := by
  have hn : NullMeasurableSet {w | c ≤ h w} ν := _root_.nullMeasurableSet_le aemeasurable_const hm
  have e := measure_add_measure_compl₀ hn
  have hc : {w | c ≤ h w}ᶜ = {w | h w < c} := by ext w; simp [not_le]
  rw [hc, measure_univ] at e
  have := congrArg ENNReal.toReal e
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at this
  linarith

lemma key (T : Set α) (h : α → ℝ) (hmono : MonotoneOn h T)
    (ν₁ ν₂ ν₃ ν₄ : Measure α) (p₁ : IsProbabilityMeasure ν₁) (p₂ : IsProbabilityMeasure ν₂)
    (p₃ : IsProbabilityMeasure ν₃) (p₄ : IsProbabilityMeasure ν₄)
    (hT₁ : ν₁ Tᶜ = 0) (hT₂ : ν₂ Tᶜ = 0) (hT₃ : ν₃ Tᶜ = 0) (hT₄ : ν₄ Tᶜ = 0)
    (hi₁ : Integrable h ν₁) (hi₂ : Integrable h ν₂) (hi₃ : Integrable h ν₃)
    (hi₄ : Integrable h ν₄)
    (hU : ∀ U : Set α, IsUpperSet U →
      (ν₁ U).toReal + (ν₂ U).toReal ≤ (ν₃ U).toReal + (ν₄ U).toReal) :
    ∫ w, h w ∂ν₁ + ∫ w, h w ∂ν₂ ≤ ∫ w, h w ∂ν₃ + ∫ w, h w ∂ν₄ := by
  have hlt : ∀ c : ℝ, ν₁ {w | c < h w} + ν₂ {w | c < h w} ≤
      ν₃ {w | c < h w} + ν₄ {w | c < h w} := by
    intro c
    have hA : ∀ a ∈ {w | c < h w} ∩ T, ∀ b ∈ T, a ≤ b → b ∈ {w | c < h w} :=
      fun a ha b hb hab => lt_of_lt_of_le ha.1 (hmono ha.2 hb hab)
    rw [meas_eq_upper ν₁ T hT₁ _ hA, meas_eq_upper ν₂ T hT₂ _ hA, meas_eq_upper ν₃ T hT₃ _ hA,
      meas_eq_upper ν₄ T hT₄ _ hA]
    exact real_to_ennreal_ineq (measure_ne_top _ _) (measure_ne_top _ _) (measure_ne_top _ _)
      (measure_ne_top _ _) (hU _ (upperClosure _).upper)
  have hle : ∀ c : ℝ, (ν₁ {w | c ≤ h w}).toReal + (ν₂ {w | c ≤ h w}).toReal ≤
      (ν₃ {w | c ≤ h w}).toReal + (ν₄ {w | c ≤ h w}).toReal := by
    intro c
    have hA : ∀ a ∈ {w | c ≤ h w} ∩ T, ∀ b ∈ T, a ≤ b → b ∈ {w | c ≤ h w} :=
      fun a ha b hb hab => le_trans ha.1 (hmono ha.2 hb hab)
    rw [meas_eq_upper ν₁ T hT₁ _ hA, meas_eq_upper ν₂ T hT₂ _ hA, meas_eq_upper ν₃ T hT₃ _ hA,
      meas_eq_upper ν₄ T hT₄ _ hA]
    exact hU _ (upperClosure _).upper
  have hneg : ∀ t : ℝ, ν₃ {w | t < -h w} + ν₄ {w | t < -h w} ≤
      ν₁ {w | t < -h w} + ν₂ {w | t < -h w} := by
    intro t
    have e : {w | t < -h w} = {w | h w < -t} := by
      ext w; simp only [mem_setOf_eq]; constructor <;> intro hh <;> linarith
    rw [e]
    apply real_to_ennreal_ineq (measure_ne_top _ _) (measure_ne_top _ _) (measure_ne_top _ _)
      (measure_ne_top _ _)
    rw [compl_toReal ν₁ p₁ h hi₁.aemeasurable, compl_toReal ν₂ p₂ h hi₂.aemeasurable,
      compl_toReal ν₃ p₃ h hi₃.aemeasurable, compl_toReal ν₄ p₄ h hi₄.aemeasurable]
    linarith [hle (-t)]
  have hP : ∫⁻ w, ENNReal.ofReal (h w) ∂ν₁ + ∫⁻ w, ENNReal.ofReal (h w) ∂ν₂ ≤
      ∫⁻ w, ENNReal.ofReal (h w) ∂ν₃ + ∫⁻ w, ENNReal.ofReal (h w) ∂ν₄ := by
    rw [pos_layer ν₁ h hi₁.aemeasurable, pos_layer ν₂ h hi₂.aemeasurable,
      pos_layer ν₃ h hi₃.aemeasurable, pos_layer ν₄ h hi₄.aemeasurable,
      ← lintegral_add_left (anti_meas ν₁ h), ← lintegral_add_left (anti_meas ν₃ h)]
    exact lintegral_mono fun t => hlt t
  have hN : ∫⁻ w, ENNReal.ofReal (-h w) ∂ν₃ + ∫⁻ w, ENNReal.ofReal (-h w) ∂ν₄ ≤
      ∫⁻ w, ENNReal.ofReal (-h w) ∂ν₁ + ∫⁻ w, ENNReal.ofReal (-h w) ∂ν₂ := by
    rw [pos_layer ν₁ (fun w => -h w) hi₁.aemeasurable.neg,
      pos_layer ν₂ (fun w => -h w) hi₂.aemeasurable.neg,
      pos_layer ν₃ (fun w => -h w) hi₃.aemeasurable.neg,
      pos_layer ν₄ (fun w => -h w) hi₄.aemeasurable.neg,
      ← lintegral_add_left (anti_meas ν₁ (fun w => -h w)),
      ← lintegral_add_left (anti_meas ν₃ (fun w => -h w))]
    exact lintegral_mono fun t => hneg t
  have f₁ := hi₁.lintegral_lt_top
  have f₂ := hi₂.lintegral_lt_top
  have f₃ := hi₃.lintegral_lt_top
  have f₄ := hi₄.lintegral_lt_top
  have g₁ : ∫⁻ x, ENNReal.ofReal (-h x) ∂ν₁ < ⊤ := hi₁.neg.lintegral_lt_top
  have g₂ : ∫⁻ x, ENNReal.ofReal (-h x) ∂ν₂ < ⊤ := hi₂.neg.lintegral_lt_top
  have g₃ : ∫⁻ x, ENNReal.ofReal (-h x) ∂ν₃ < ⊤ := hi₃.neg.lintegral_lt_top
  have g₄ : ∫⁻ x, ENNReal.ofReal (-h x) ∂ν₄ < ⊤ := hi₄.neg.lintegral_lt_top
  have hP' := ennreal_to_real_ineq f₁.ne f₂.ne f₃.ne f₄.ne hP
  have hN' := ennreal_to_real_ineq g₃.ne g₄.ne g₁.ne g₂.ne hN
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₁,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₂,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₃,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₄]
  linarith

end P03c74cda

open MeasureTheory in
theorem solution {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (hSlattice : ∀ i, IsSublattice (S i))
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (hμsupp : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → μ i x t (T (i + 1))ᶜ = 0)
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hrsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => r i p.1 p.2) (S i))
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x))
    (hFsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.MDP.StochasticallySupermodularOn (S i)
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => μ i p.1 p.2)) :
    (∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g i p.1 p.2) (S i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → Supermodularity.Monotonicity.SupermodularOn (f i) (T i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t t' : Fin m → ℝ⦄, t ∈ T i → t' ∈ T i → t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder
        {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}
        {x : Fin n → ℝ | x ∈ X i t' ∧ ∀ y ∈ X i t', g i y t' ≤ g i x t'}) ∧
    (∃ xg xl : ℕ → (Fin m → ℝ) → (Fin n → ℝ),
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsGreatest {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xg i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsLeast {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xl i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xg i) (T i)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xl i) (T i))) := by
  classical
  have hγ : 0 ≤ 1 / (1 + β) := by positivity
  have memS : ∀ i x t, (x, t) ∈ S i ↔ t ∈ T i ∧ x ∈ X i t := by
    intro i x t; rw [hS i]; rfl
  have gmono : ∀ i, 1 ≤ i → i ≤ k → (i < k → MonotoneOn (f (i + 1)) (T (i + 1))) →
      ∀ x t t', (x, t) ∈ S i → (x, t') ∈ S i → t ≤ t' → g i x t ≤ g i x t' := by
    intro i h1 hk hnext x t t' hxt hxt' htt'
    rcases lt_or_eq_of_le hk with hlt | heq
    · rw [hg i h1 hlt x t hxt, hg i h1 hlt x t' hxt']
      have hr : r i x t ≤ r i x t' := hrmono i h1 hk x hxt hxt' htt'
      have hI := P03c74cda.key (T (i + 1)) (f (i + 1)) (hnext hlt) (μ i x t) (μ i x t)
        (μ i x t') (μ i x t') (hμprob i x t) (hμprob i x t) (hμprob i x t') (hμprob i x t')
        (hμsupp i h1 hlt x t hxt) (hμsupp i h1 hlt x t hxt) (hμsupp i h1 hlt x t' hxt')
        (hμsupp i h1 hlt x t' hxt')
        (hfint i h1 hlt x t hxt) (hfint i h1 hlt x t hxt) (hfint i h1 hlt x t' hxt')
        (hfint i h1 hlt x t' hxt')
        (fun U hU => by
          have h2 : (μ i x t U).toReal ≤ (μ i x t' U).toReal :=
            hFmono i h1 hk x hU hxt hxt' htt'
          linarith)
      have hI' : ∫ w, f (i + 1) w ∂(μ i x t) ≤ ∫ w, f (i + 1) w ∂(μ i x t') := by linarith
      have := mul_le_mul_of_nonneg_left hI' hγ
      linarith
    · subst heq
      rw [hgk, hgk]
      exact hrmono i h1 hk x hxt hxt' htt'
  have fmono_step : ∀ i, 1 ≤ i → i ≤ k → (i < k → MonotoneOn (f (i + 1)) (T (i + 1))) →
      MonotoneOn (f i) (T i) := by
    intro i h1 hk hnext t ht t' ht' htt'
    obtain ⟨⟨x, hx, hxe⟩, _⟩ := hf i h1 hk t ht
    have hx' : x ∈ X i t' := hXsub i h1 hk ht ht' htt' (Finset.mem_coe.1 hx)
    have hxt : (x, t) ∈ S i := (memS i x t).2 ⟨ht, Finset.mem_coe.1 hx⟩
    have hxt' : (x, t') ∈ S i := (memS i x t').2 ⟨ht', hx'⟩
    have h3 := gmono i h1 hk hnext x t t' hxt hxt' htt'
    have hub : g i x t' ≤ f i t' := (hf i h1 hk t' ht').2 ⟨x, Finset.mem_coe.2 hx', rfl⟩
    have hxe' : g i x t = f i t := hxe
    linarith
  have aux : ∀ j i, k - i = j → 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) := by
    intro j
    induction j with
    | zero =>
      intro i hj h1 hk
      exact fmono_step i h1 hk (fun hlt => by omega)
    | succ j ih =>
      intro i hj h1 hk
      exact fmono_step i h1 hk (fun hlt => ih (i + 1) (by omega) (by omega) (by omega))
  have fmono : ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) :=
    fun i h1 hk => aux (k - i) i rfl h1 hk
  have gsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g i p.1 p.2) (S i) := by
    intro i h1 hk
    rcases lt_or_eq_of_le hk with hlt | heq
    · intro p hp q hq
      have hsup : p ⊔ q ∈ S i := (hSlattice i).supClosed hp hq
      have hinf : p ⊓ q ∈ S i := (hSlattice i).infClosed hp hq
      show g i p.1 p.2 + g i q.1 q.2 ≤ g i (p ⊔ q).1 (p ⊔ q).2 + g i (p ⊓ q).1 (p ⊓ q).2
      rw [hg i h1 hlt _ _ hp, hg i h1 hlt _ _ hq, hg i h1 hlt (p ⊔ q).1 (p ⊔ q).2 hsup,
        hg i h1 hlt (p ⊓ q).1 (p ⊓ q).2 hinf]
      have hr : r i p.1 p.2 + r i q.1 q.2 ≤ r i (p ⊔ q).1 (p ⊔ q).2 + r i (p ⊓ q).1 (p ⊓ q).2 :=
        hrsuper i h1 hk hp hq
      have hI := P03c74cda.key (T (i + 1)) (f (i + 1)) (fmono (i + 1) (by omega) (by omega))
        (μ i p.1 p.2) (μ i q.1 q.2) (μ i (p ⊔ q).1 (p ⊔ q).2) (μ i (p ⊓ q).1 (p ⊓ q).2)
        (hμprob _ _ _) (hμprob _ _ _) (hμprob _ _ _) (hμprob _ _ _)
        (hμsupp i h1 hlt _ _ hp) (hμsupp i h1 hlt _ _ hq) (hμsupp i h1 hlt _ _ hsup)
        (hμsupp i h1 hlt _ _ hinf)
        (hfint i h1 hlt _ _ hp) (hfint i h1 hlt _ _ hq) (hfint i h1 hlt _ _ hsup)
        (hfint i h1 hlt _ _ hinf)
        (fun U hU => hFsuper i h1 hk hU hp hq)
      have hγI := mul_le_mul_of_nonneg_left hI hγ
      rw [mul_add, mul_add] at hγI
      linarith
    · subst heq
      have e : (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g i p.1 p.2) =
          fun p => r i p.1 p.2 := funext fun p => hgk _ _
      rw [e]
      exact hrsuper i h1 hk
  have fsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn (f i) (T i) := by
    intro i h1 hk t ht t' ht'
    obtain ⟨⟨x, hx, hxe⟩, _⟩ := hf i h1 hk t ht
    obtain ⟨⟨x', hx', hxe'⟩, _⟩ := hf i h1 hk t' ht'
    have hp : (x, t) ∈ S i := (memS i x t).2 ⟨ht, Finset.mem_coe.1 hx⟩
    have hq : (x', t') ∈ S i := (memS i x' t').2 ⟨ht', Finset.mem_coe.1 hx'⟩
    have hsup : (x ⊔ x', t ⊔ t') ∈ S i := (hSlattice i).supClosed hp hq
    have hinf : (x ⊓ x', t ⊓ t') ∈ S i := (hSlattice i).infClosed hp hq
    obtain ⟨hs1, hs2⟩ := (memS i _ _).1 hsup
    obtain ⟨hi1, hi2⟩ := (memS i _ _).1 hinf
    have hsm : g i x t + g i x' t' ≤ g i (x ⊔ x') (t ⊔ t') + g i (x ⊓ x') (t ⊓ t') :=
      gsuper i h1 hk hp hq
    have u1 : g i (x ⊔ x') (t ⊔ t') ≤ f i (t ⊔ t') :=
      (hf i h1 hk _ hs1).2 ⟨_, Finset.mem_coe.2 hs2, rfl⟩
    have u2 : g i (x ⊓ x') (t ⊓ t') ≤ f i (t ⊓ t') :=
      (hf i h1 hk _ hi1).2 ⟨_, Finset.mem_coe.2 hi2, rfl⟩
    have e1 : g i x t = f i t := hxe
    have e2 : g i x' t' = f i t' := hxe'
    show f i t + f i t' ≤ f i (t ⊔ t') + f i (t ⊓ t')
    linarith
  have csub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t t' : Fin m → ℝ⦄, t ∈ T i → t' ∈ T i → t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder
        {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}
        {x : Fin n → ℝ | x ∈ X i t' ∧ ∀ y ∈ X i t', g i y t' ≤ g i x t'} := by
    intro i h1 hk t t' ht ht' htt' a ha b hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hp : (a, t) ∈ S i := (memS i a t).2 ⟨ht, ha1⟩
    have hq : (b, t') ∈ S i := (memS i b t').2 ⟨ht', hb1⟩
    have hsup : (a ⊔ b, t ⊔ t') ∈ S i := (hSlattice i).supClosed hp hq
    have hinf : (a ⊓ b, t ⊓ t') ∈ S i := (hSlattice i).infClosed hp hq
    have hsm : g i a t + g i b t' ≤ g i (a ⊔ b) (t ⊔ t') + g i (a ⊓ b) (t ⊓ t') :=
      gsuper i h1 hk hp hq
    have e1 : t ⊔ t' = t' := sup_eq_right.2 htt'
    have e2 : t ⊓ t' = t := inf_eq_left.2 htt'
    rw [e1] at hsup hsm
    rw [e2] at hinf hsm
    obtain ⟨_, hs2⟩ := (memS i _ _).1 hsup
    obtain ⟨_, hi2⟩ := (memS i _ _).1 hinf
    have u1 := hb2 _ hs2
    have u2 := ha2 _ hi2
    refine ⟨⟨hi2, fun y hy => ?_⟩, ⟨hs2, fun y hy => ?_⟩⟩
    · have := ha2 y hy; linarith
    · have := hb2 y hy; linarith
  have hex : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      (∃ x, IsGreatest {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} x) ∧
      (∃ x, IsLeast {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} x) := by
    intro i h1 hk t ht
    have hfin : {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}.Finite :=
      (X i t).finite_toSet.subset (fun x hx => Finset.mem_coe.2 hx.1)
    obtain ⟨⟨x, hx, hxe⟩, hub⟩ := hf i h1 hk t ht
    have hne : {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}.Nonempty := by
      refine ⟨x, Finset.mem_coe.1 hx, fun y hy => ?_⟩
      have e : g i x t = f i t := hxe
      rw [e]
      exact hub ⟨y, Finset.mem_coe.2 hy, rfl⟩
    have hcl := csub i h1 hk ht ht le_rfl
    constructor
    · obtain ⟨M, hM⟩ := hfin.exists_maximal hne
      refine ⟨M, hM.prop, fun y hy => ?_⟩
      have h2 := (hcl hM.prop hy).2
      exact le_sup_right.trans (hM.2 h2 le_sup_left)
    · obtain ⟨M, hM⟩ := hfin.exists_minimal hne
      refine ⟨M, hM.prop, fun y hy => ?_⟩
      have h2 := (hcl hy hM.prop).1
      exact (hM.2 h2 inf_le_right).trans inf_le_left
  refine ⟨gsuper, fsuper, fun i h1 hk t t' ht ht' htt' => csub i h1 hk ht ht' htt', ?_⟩
  refine ⟨fun i t => if h : ∃ x, IsGreatest
      {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} x then h.choose else 0,
    fun i t => if h : ∃ x, IsLeast
      {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} x then h.choose else 0,
    ?_, ?_, ?_, ?_⟩
  · intro i h1 hk t ht
    have h := (hex i h1 hk t ht).1
    simp only [dif_pos h]
    exact h.choose_spec
  · intro i h1 hk t ht
    have h := (hex i h1 hk t ht).2
    simp only [dif_pos h]
    exact h.choose_spec
  · intro i h1 hk t ht t' ht' htt'
    have h := (hex i h1 hk t ht).1
    have h' := (hex i h1 hk t' ht').1
    simp only [dif_pos h, dif_pos h']
    have hs := (csub i h1 hk ht ht' htt' h.choose_spec.1 h'.choose_spec.1).2
    exact le_sup_left.trans (h'.choose_spec.2 hs)
  · intro i h1 hk t ht t' ht' htt'
    have h := (hex i h1 hk t ht).2
    have h' := (hex i h1 hk t' ht').2
    simp only [dif_pos h, dif_pos h']
    have hs := (csub i h1 hk ht ht' htt' h.choose_spec.1 h'.choose_spec.1).1
    exact (h.choose_spec.2 hs).trans inf_le_right
