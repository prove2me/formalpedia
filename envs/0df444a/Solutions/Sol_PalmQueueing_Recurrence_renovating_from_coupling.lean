-- Prove2me | solution 1 for PalmQueueing.Recurrence.renovating_from_coupling
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:52:11.009035+00:00
-- url     : https://prove2.me/submissions/d6b00ef2-a6b6-4685-8ef9-929a117c29a4

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Renovating

open MeasureTheory Filter Topology PalmQueueing.Recurrence

section Counterexample

open Classical in
private noncomputable def hCounter (x : Fin 1 → ℝ) (z : ℕ) : Fin 1 → ℝ :=
  fun _ =>
    if x 0 = 1 then 1
    else if x 0 = 0 then (if z ≤ 1 then 1 else 2)
    else if ∃ k : ℕ, 2 ≤ k ∧ x 0 = (k : ℝ) then
      if z ≤ Nat.floor (x 0) then 1 else ((Nat.floor (x 0) + 1 : ℕ) : ℝ)
    else 0

private noncomputable def WCCounter : ℕ → ℕ → Fin 1 → ℝ
  | 0, _ => fun _ => 0
  | n + 1, ω => hCounter (WCCounter n ω) ω

private lemma hCounter_nonneg (x : Fin 1 → ℝ) (z : ℕ) : 0 ≤ hCounter x z := by
  intro i
  dsimp [hCounter]
  split_ifs <;> positivity

private lemma WCCounter_eq (n : ℕ) (hn : 1 ≤ n) (ω : ℕ) :
    WCCounter n ω 0 = if ω ≤ n then 1 else ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm
      simp [WCCounter, hCounter]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      specialize ih hm1
      rw [WCCounter, hCounter]
      by_cases hω : ω ≤ m
      · have h1 : WCCounter m ω 0 = 1 := by simp [ih, hω]
        have hω' : ω ≤ m + 1 := Nat.le_succ_of_le hω
        simp [h1, hω']
      · have hval : WCCounter m ω 0 = ((m + 1 : ℕ) : ℝ) := by simp [ih, hω]
        have hne1 : WCCounter m ω 0 ≠ 1 := by
          rw [hval]
          exact_mod_cast (by omega : m + 1 ≠ 1)
        have hne0 : WCCounter m ω 0 ≠ 0 := by
          rw [hval]
          exact_mod_cast (by omega : m + 1 ≠ 0)
        have hex : ∃ k : ℕ, 2 ≤ k ∧ WCCounter m ω 0 = (k : ℝ) :=
          ⟨m + 1, by omega, hval⟩
        have hfl : Nat.floor (WCCounter m ω 0) = m + 1 := by
          rw [hval, Nat.floor_natCast]
        simp [hne1, hne0, hex, hfl]

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {K : ℕ} {F : Type}
      (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (_herg : Ergodic θ P0)
      (h : (Fin K → ℝ) → F → Fin K → ℝ)
      (_hnonneg : ∀ (x : Fin K → ℝ) (z : F), 0 ≤ x → 0 ≤ h x z)
      (xi : ℕ → Ω → F) (xi0 : Ω → F)
      (_hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
      (C : Fin K → ℝ) (_hC : 0 ≤ C)
      (WC : ℕ → Ω → Fin K → ℝ)
      (_hWC : IsRecurrentSequence h xi (fun _ => C) WC)
      (Z : Ω → Fin K → ℝ)
      (_hZ : ∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω))
      (_hcouple : StrongBackwardsCoupling P0 θ WC Z),
      ∃ (m : ℕ) (Phi : (Fin m → F) → Fin K → ℝ) (A : ℕ → Set Ω),
        (∀ n, MeasurableSet (A n)) ∧
        (∀ n : ℕ, A n = ((θ : Ω → Ω)^[n]) ⁻¹' A 0) ∧
        0 < P0 (A 0) ∧
        IsRenovating xi WC m Phi A) := by
  intro H
  let : MeasurableSpace ℕ := ⊥
  let P0 : Measure ℕ := Measure.dirac 0
  have : IsProbabilityMeasure P0 := inferInstance
  let θ : ℕ ≃ᵐ ℕ := MeasurableEquiv.refl ℕ
  have hθid : (θ : ℕ → ℕ) = id := rfl
  have hθsymmid : (θ.symm : ℕ → ℕ) = id := rfl
  have herg : Ergodic θ P0 := by
    refine ⟨MeasurePreserving.id P0, ⟨fun s hs _ => ?_⟩⟩
    rw [MeasurableSpace.measurableSet_bot_iff] at hs
    rcases hs with rfl | rfl
    · exact eventuallyConst_set'.mpr (Or.inl (by simp))
    · exact eventuallyConst_set'.mpr (Or.inr (by simp))
  have hcouple : StrongBackwardsCoupling P0 θ WCCounter (fun _ _ => 1) := by
    filter_upwards with ω
    refine ⟨max 1 ω, fun k => ?_⟩
    ext i
    fin_cases i
    have h1 : 1 ≤ max 1 ω + k := by omega
    have h2 : ω ≤ max 1 ω + k := by omega
    rw [hθsymmid, Function.iterate_id, id_eq]
    change WCCounter (max 1 ω + k) ω 0 = 1
    rw [WCCounter_eq _ h1]
    simp [h2]
  have hZ : ∀ᵐ ω ∂P0, (fun _ _ => (1 : ℝ)) ((θ : ℕ → ℕ) ω) = hCounter (fun _ => 1) ω := by
    filter_upwards with ω
    ext i
    simp [hCounter]
  obtain ⟨m, Phi, A, hAmeas, hAshift, hApos, hm1, hren⟩ :=
    H P0 θ herg hCounter (fun x z _ => hCounter_nonneg x z)
      (fun _ ω => ω) id (fun n ω => by rw [hθid, Function.iterate_id]; rfl)
      (fun _ => 0) (fun _ => le_rfl) WCCounter
      ⟨fun _ => rfl, fun _ _ => rfl⟩ (fun _ _ => 1) hZ hcouple
  have hA0 : A 0 = Set.univ := by
    have h := hAmeas 0
    rw [MeasurableSpace.measurableSet_bot_iff] at h
    rcases h with h0 | huniv
    · rw [h0, measure_empty] at hApos
      exact absurd hApos (lt_irrefl 0)
    · exact huniv
  have hAn : ∀ n, A n = Set.univ := fun n => by
    rw [hAshift n, hA0]
    simp
  have eq0 : WCCounter (0 + m) (m + 1) = Phi (fun _ => m + 1) :=
    hren 0 (m + 1) (by rw [hAn]; trivial)
  have eq1 : WCCounter (1 + m) (m + 1) = Phi (fun _ => m + 1) :=
    hren 1 (m + 1) (by rw [hAn]; trivial)
  have eq01 : WCCounter m (m + 1) 0 = WCCounter (m + 1) (m + 1) 0 := by
    have h := eq0.trans eq1.symm
    have h' := congrFun h 0
    simpa [Nat.add_comm] using h'
  rw [WCCounter_eq m hm1 (m + 1), WCCounter_eq (m + 1) (by omega) (m + 1)] at eq01
  have hnotle : ¬ (m + 1 ≤ m) := by omega
  simp [hnotle] at eq01
  omega


end Counterexample
