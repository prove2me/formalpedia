-- Prove2me | solution 1 for PalmQueueing.Recurrence.stability_region
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:08:22.275494+00:00
-- url     : https://prove2.me/submissions/981f7ba1-c77f-4c05-b47a-d2e8abad4f0f

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Saturation

open MeasureTheory Filter Topology PalmQueueing.Recurrence

private noncomputable def X_cex (T : ℤ → ℝ) (_ξ : ℤ → Unit) (m n : ℤ) : ℝ :=
  if n < 0 then
    if h : m ≤ n then
      (Finset.Icc m n).sup' ⟨m, Finset.left_mem_Icc.mpr h⟩
        (fun k => T k + 10 * ((n - k + 1 : ℤ) : ℝ))
    else 0
  else T n

private lemma X_cex_isMHS : IsMHS X_cex where
  local_ T T' ξ ξ' m n hmn hloc := by
    simp only [X_cex, hmn, ↓reduceDIte]
    split_ifs with hn
    · refine Finset.sup'_congr _ rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      rw [(hloc k hk.1 hk.2).1]
    · exact (hloc n hmn le_rfl).1
  causality T ξ m n _hT hmn := by
    simp only [X_cex, hmn, ↓reduceDIte]
    split_ifs with hn
    · have hmem : n ∈ Finset.Icc m n := Finset.right_mem_Icc.mpr hmn
      have hle := Finset.le_sup' (f := fun k => T k + 10 * ((n - k + 1 : ℤ) : ℝ)) hmem
      simp only [sub_self, zero_add, Int.cast_one, mul_one] at hle
      linarith
    · exact le_rfl
  externalMonotone T T' ξ m n _hT _hT' hmn hle := by
    simp only [X_cex, hmn, ↓reduceDIte]
    split_ifs with hn
    · refine Finset.sup'_le _ _ fun k hk => ?_
      calc T k + 10 * ((n - k + 1 : ℤ) : ℝ)
          ≤ T' k + 10 * ((n - k + 1 : ℤ) : ℝ) := by linarith [hle k]
        _ ≤ _ := Finset.le_sup' (f := fun k => T' k + 10 * ((n - k + 1 : ℤ) : ℝ)) hk
    · exact hle n
  homogeneous T ξ m n c _hT hmn := by
    simp only [X_cex, hmn, ↓reduceDIte]
    split_ifs with hn
    · apply le_antisymm
      · refine Finset.sup'_le _ _ fun k hk => ?_
        have h := Finset.le_sup' (f := fun k => T k + 10 * ((n - k + 1 : ℤ) : ℝ)) hk
        linarith
      · have hle : (Finset.Icc m n).sup' ⟨m, Finset.left_mem_Icc.mpr hmn⟩
            (fun k => T k + 10 * ((n - k + 1 : ℤ) : ℝ)) ≤
          (Finset.Icc m n).sup' ⟨m, Finset.left_mem_Icc.mpr hmn⟩
            (fun k => (T k + c) + 10 * ((n - k + 1 : ℤ) : ℝ)) - c := by
          refine Finset.sup'_le _ _ fun k hk => ?_
          have h := Finset.le_sup' (f := fun k => (T k + c) + 10 * ((n - k + 1 : ℤ) : ℝ)) hk
          linarith
        linarith
    · rfl
  separable T ξ m l n _hT hml hln hsep := by
    have hmn : m ≤ n := le_trans hml (le_of_lt hln)
    have hl1n : l + 1 ≤ n := hln
    simp only [X_cex, hmn, hl1n, ↓reduceDIte]
    split_ifs with hn
    · have hl : l < 0 := lt_trans hln hn
      simp only [X_cex, hl, hml, ↓reduceIte, ↓reduceDIte] at hsep
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        by_cases hkl : k ≤ l
        · have hk_mem : k ∈ Finset.Icc m l := Finset.mem_Icc.mpr ⟨hk.1, hkl⟩
          have hk_le : T k + 10 * ((l - k + 1 : ℤ) : ℝ) ≤ T (l + 1) :=
            le_trans (Finset.le_sup' (f := fun j => T j + 10 * ((l - j + 1 : ℤ) : ℝ)) hk_mem) hsep
          have hl1_mem : l + 1 ∈ Finset.Icc (l + 1) n := Finset.left_mem_Icc.mpr hl1n
          have hgoal := Finset.le_sup' (f := fun j => T j + 10 * ((n - j + 1 : ℤ) : ℝ)) hl1_mem
          have hcast : ((n - k + 1 : ℤ) : ℝ) = ((l - k + 1 : ℤ) : ℝ) + ((n - (l + 1) + 1 : ℤ) : ℝ) := by
            push_cast; ring
          linarith
        · have hk_mem : k ∈ Finset.Icc (l + 1) n := Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
          exact Finset.le_sup' (f := fun j => T j + 10 * ((n - j + 1 : ℤ) : ℝ)) hk_mem
      · refine Finset.sup'_le _ _ fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        have hk_mem : k ∈ Finset.Icc m n := Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
        exact Finset.le_sup' (f := fun j => T j + 10 * ((n - j + 1 : ℤ) : ℝ)) hk_mem
    · rfl

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {E : Type} [MeasurableSpace E]
      (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω)
      (_herg : Ergodic θ P0)
      (X : (ℤ → ℝ) → (ℤ → E) → ℤ → ℤ → ℝ) (_hX : IsMHS X)
      (_hXmeas : ∀ m n : ℤ, Measurable (fun p : (ℤ → ℝ) × (ℤ → E) => X p.1 p.2 m n))
      (T : Ω → ℤ → ℝ) (ξ : Ω → ℤ → E)
      (_hTmeas : ∀ n : ℤ, Measurable (fun ω => T ω n))
      (_hξmeas : ∀ n : ℤ, Measurable (fun ω => ξ ω n))
      (_hT : ∀ ω : Ω, Monotone (T ω))
      (_hT0 : ∀ ω : Ω, T ω 0 = 0)
      (_hTθ : ∀ (ω : Ω) (n : ℤ), T (θ ω) n = T ω (n + 1) - T ω 1)
      (_hξθ : ∀ (ω : Ω) (n : ℤ), ξ (θ ω) n = ξ ω (n + 1))
      (lam : ℝ) (_hlam : 0 < lam)
      (_hlam_def : ∀ n : ℤ, ∫ ω, (T ω (n + 1) - T ω n) ∂P0 = lam⁻¹)
      (_hZint : ∀ n : ℤ, Integrable (fun ω => mhsZ X (T ω) (ξ ω) n n) P0)
      (gam0 : ℝ) (_hgam0 : IsGrowthRate P0 X T ξ 0 gam0),
      ((∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => mhsZ X (T ω) (ξ ω) (-(n : ℤ)) 0) atTop atTop) →
        1 ≤ lam * gam0) ∧
      (1 < lam * gam0 →
        ∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => mhsZ X (T ω) (ξ ω) (-(n : ℤ)) 0) atTop atTop)) := by
  intro H
  let P0 : Measure Unit := Measure.dirac ()
  let θ : Unit ≃ᵐ Unit := MeasurableEquiv.refl Unit
  have herg : Ergodic θ P0 :=
    { toMeasurePreserving := MeasurePreserving.id P0
      aeconst_set := fun s _ _ =>
        eventuallyConst_iff_exists_eventuallyEq.mpr
          ⟨s (), Filter.Eventually.of_forall fun x => by cases x; rfl⟩ }
  have hXmeas : ∀ m n : ℤ, Measurable (fun p : (ℤ → ℝ) × (ℤ → Unit) => X_cex p.1 p.2 m n) := by
    intro m n
    simp only [X_cex]
    split_ifs with hn hmn
    · convert Finset.measurable_sup' (s := Finset.Icc m n)
          (hs := ⟨m, Finset.left_mem_Icc.mpr hmn⟩)
          (f := fun k (p : (ℤ → ℝ) × (ℤ → Unit)) => p.1 k + 10 * ((n - k + 1 : ℤ) : ℝ))
          (fun k _ => ((measurable_pi_apply k).comp measurable_fst).add measurable_const) using 1
      ext p
      exact (Finset.sup'_apply (H := ⟨m, Finset.left_mem_Icc.mpr hmn⟩)
        (f := fun k (p : (ℤ → ℝ) × (ℤ → Unit)) => p.1 k + 10 * ((n - k + 1 : ℤ) : ℝ))
        (b := p)).symm
    · exact measurable_const
    · exact (measurable_pi_apply n).comp measurable_fst
  let T : Unit → ℤ → ℝ := fun _ n => (n : ℝ)
  let ξ : Unit → ℤ → Unit := fun _ _ => ()
  have hgam0 : IsGrowthRate P0 X_cex T ξ 0 10 := by
    refine ⟨by norm_num, ?_⟩
    filter_upwards with ω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hle : -(n : ℤ) ≤ -1 := by omega
    have hneg : (-1 : ℤ) < 0 := by omega
    have hval : X_cex (scalePoints 0 (T ω)) (ξ ω) (-(n : ℤ)) (-1) = 10 * (n : ℝ) := by
      simp only [X_cex, hneg, hle, ↓reduceIte, ↓reduceDIte, scalePoints, zero_mul, zero_add]
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        have : ((-1 - k + 1 : ℤ) : ℝ) ≤ (n : ℝ) := by
          have : -1 - k + 1 ≤ (n : ℤ) := by omega
          exact_mod_cast this
        linarith
      · have hmem : -(n : ℤ) ∈ Finset.Icc (-(n : ℤ)) (-1) := Finset.left_mem_Icc.mpr hle
        have := Finset.le_sup' (f := fun k => 10 * ((-1 - k + 1 : ℤ) : ℝ)) hmem
        have hcast : ((-1 - -(n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
        linarith
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [mhsZ, hval, scalePoints, zero_mul, sub_zero]
    field_simp
  have hres := H P0 θ herg X_cex X_cex_isMHS hXmeas T ξ
    (fun _ => measurable_const) (fun _ => measurable_const)
    (fun _ a b hab => Int.cast_le.mpr hab)
    (fun _ => Int.cast_zero)
    (fun _ n => by simp [T, θ])
    (fun _ _ => rfl)
    1 zero_lt_one
    (fun n => by simp [T, P0])
    (fun n => by
      have : (fun ω : Unit => mhsZ X_cex (T ω) (ξ ω) n n) = fun _ => mhsZ X_cex (T ()) (ξ ()) n n := by
        ext ω; cases ω; rfl
      rw [this]
      exact integrable_const _)
    10 hgam0
  have h2 := hres.2 (by norm_num)
  rw [ae_dirac_iff (.of_discrete)] at h2
  have h0 : (fun n : ℕ => mhsZ X_cex (T ()) (ξ ()) (-(n : ℤ)) 0) = fun _ => 0 := by
    ext n
    simp [mhsZ, X_cex, T]
  rw [h0] at h2
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 0 := h2 (eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h1
  linarith [hN N le_rfl]

