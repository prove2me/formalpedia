-- Prove2me | solution 1 for RiskFunctionals.NestedAVaR.nested_le_multiperiod_final
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:02:02.735718+00:00
-- url     : https://prove2.me/submissions/857c0f1e-b029-4e8a-9f41-8d5f2739c841

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk

open RiskFunctionals.NestedAVaR

open MeasureTheory

theorem g79t_univ {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} {α : ℝ}
    {X V : Ω → ℝ} (h : IsConditionalAVaR m P α X V) :
    ((∫ ω, V ω ∂P : ℝ) : EReal) = ⨅ (Z : Ω → ℝ) (_ : Measurable Z ∧
            (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (Set.univ : Set Ω).indicator (fun _ => 1 / α) ω) ∧
            P[Z|m] =ᵐ[P] (Set.univ : Set Ω).indicator (fun _ => (1 : ℝ))),
          ((∫ ω, X ω * Z ω ∂P : ℝ) : EReal) := by
  have := h.2.2 Set.univ MeasurableSet.univ
  rwa [setIntegral_univ] at this

theorem g79t_feas {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) {P : Measure[mΩ] Ω}
    [IsProbabilityMeasure P] {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    Measurable (fun _ : Ω => (1 : ℝ)) ∧
      (∀ᵐ ω ∂P, 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ (Set.univ : Set Ω).indicator (fun _ => 1 / α) ω) ∧
      P[(fun _ : Ω => (1 : ℝ))|m] =ᵐ[P] (Set.univ : Set Ω).indicator (fun _ => (1 : ℝ)) := by
  refine ⟨measurable_const, Filter.Eventually.of_forall fun ω => ⟨zero_le_one, ?_⟩, ?_⟩
  · rw [Set.indicator_univ]; exact one_le_one_div hα₀ hα₁
  · rw [Set.indicator_univ, condExp_const hm]

theorem g79t_le {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) {P : Measure[mΩ] Ω}
    [IsProbabilityMeasure P] {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    {X V : Ω → ℝ} (h : IsConditionalAVaR m P α X V) : ∫ ω, V ω ∂P ≤ ∫ ω, X ω ∂P := by
  have h1 := g79t_univ h
  have h2 : ((∫ ω, V ω ∂P : ℝ) : EReal) ≤ ((∫ ω, X ω * 1 ∂P : ℝ) : EReal) := by
    rw [h1]; exact iInf₂_le (fun _ : Ω => (1:ℝ)) (g79t_feas hm hα₀ hα₁)
  simpa using h2

theorem g79t_eq {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} {α : ℝ}
    {X X' V V' : Ω → ℝ} (h : IsConditionalAVaR m P α X V) (h' : IsConditionalAVaR m P α X' V')
    (hX : X =ᵐ[P] X') : ∫ ω, V ω ∂P = ∫ ω, V' ω ∂P := by
  have e : ((∫ ω, V ω ∂P : ℝ) : EReal) = ((∫ ω, V' ω ∂P : ℝ) : EReal) := by
    rw [g79t_univ h, g79t_univ h']
    refine iInf_congr fun Z => iInf_congr fun _ => ?_
    rw [integral_congr_ae (hX.mono fun ω hω => show X ω * Z ω = X' ω * Z ω by rw [hω])]
  exact_mod_cast e

theorem g79t_zero {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) {P : Measure[mΩ] Ω}
    [IsProbabilityMeasure P] {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    {X V : Ω → ℝ} (h : IsConditionalAVaR m P α X V) (hX : X =ᵐ[P] 0) : ∫ ω, V ω ∂P = 0 := by
  have h0 : ∀ Z : Ω → ℝ, ∫ ω, X ω * Z ω ∂P = 0 := fun Z => by
    rw [integral_congr_ae (g := fun _ => (0:ℝ))
      (hX.mono fun ω hω => show X ω * Z ω = 0 by rw [hω, Pi.zero_apply, zero_mul]), integral_zero]
  have e : ((∫ ω, V ω ∂P : ℝ) : EReal) = ((0 : ℝ) : EReal) := by
    rw [g79t_univ h]
    apply le_antisymm
    · have := iInf₂_le (f := fun (Z : Ω → ℝ) (_ : Measurable Z ∧
            (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (Set.univ : Set Ω).indicator (fun _ => 1 / α) ω) ∧
            P[Z|m] =ᵐ[P] (Set.univ : Set Ω).indicator (fun _ => (1 : ℝ))) =>
          ((∫ ω, X ω * Z ω ∂P : ℝ) : EReal)) _ (g79t_feas hm hα₀ hα₁)
      rwa [h0] at this
    · exact le_iInf₂ fun Z _ => by rw [h0]
  exact_mod_cast e

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P 1 (Y t))
    (hfinal : ∀ t ∈ Finset.Icc 1 (T - 1), Y t =ᵐ[P] 0) (vn vm : ℝ)
    (hn : IsNestedAVaR ℱ P α T Y vn)
    (hm : IsMultiPeriodAVaR ℱ P (fun _ => α) (fun _ => 1) T Y vm) :
    vn ≤ vm := by
  obtain ⟨A, hA, rfl⟩ := hn
  obtain ⟨V, hV, rfl⟩ := hm
  have hYi : ∀ t ∈ Finset.Icc 1 T, Integrable (Y t) P := fun t ht =>
    (hY t ht).2.integrable le_rfl
  -- composition lemma
  have hcomp : ∀ t, t ≤ T → ∀ X, Integrable X P →
      Integrable (composition A t X) P ∧ ∫ ω, composition A t X ω ∂P ≤ ∫ ω, X ω ∂P := by
    intro t
    induction t with
    | zero => intro _ X hX; exact ⟨hX, le_rfl⟩
    | succ t ih =>
      intro ht X hX
      have hc := hA t (by omega) X hX
      have h2 := ih (by omega) (A t X) hc.2.1
      refine ⟨h2.1, ?_⟩
      show ∫ ω, composition A t (A t X) ω ∂P ≤ _
      exact h2.2.trans (g79t_le (ℱ.le t) hα₀ hα₁ hc)
  cases T with
  | zero => simp [compositionValue, composition]
  | succ n =>
    set S : Ω → ℝ := fun ω => ∑ t ∈ Finset.Icc 1 (n + 1), Y t ω with hS
    have hSi : Integrable S P := integrable_finset_sum _ hYi
    have hcS := hA n (by omega) S hSi
    have hlast := hV (n + 1) (by simp)
    simp only [Nat.add_sub_cancel] at hlast
    have hSY : S =ᵐ[P] Y (n + 1) := by
      have hall : ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 n, Y t ω = 0 :=
        (Filter.eventually_all_finset _).2 fun t ht => by
          have := hfinal t (by simpa using ht); exact this
      filter_upwards [hall] with ω hω
      simp only [hS]
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_eq_zero hω, zero_add]
    have hEq : ∫ ω, A n S ω ∂P = ∫ ω, V (n + 1) ω ∂P := g79t_eq hcS hlast hSY
    have hvn : compositionValue P A (n + 1) S ≤ ∫ ω, A n S ω ∂P :=
      (hcomp n (by omega) (A n S) hcS.2.1).2
    have hsum : ∑ t ∈ Finset.Icc 1 (n + 1), (fun _ => (1:ℝ)) t * ∫ ω, V t ω ∂P
        = ∫ ω, V (n + 1) ω ∂P := by
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [Finset.sum_eq_zero fun t ht => ?_]
      · simp
      · have ht' : t ∈ Finset.Icc 1 (n + 1) := by
          simp only [Finset.mem_Icc] at ht ⊢; omega
        have := g79t_zero (ℱ.le _) hα₀ hα₁ (hV t ht') (hfinal t (by simpa using ht))
        simp [this]
    rw [hsum, ← hEq]
    exact hvn
