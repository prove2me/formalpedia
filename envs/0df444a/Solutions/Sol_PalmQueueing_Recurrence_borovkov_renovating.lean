-- Prove2me | solution 1 for PalmQueueing.Recurrence.borovkov_renovating
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:28:01.606993+00:00
-- url     : https://prove2.me/submissions/0ff017a0-9d37-4a22-ac0d-7c0ad672b797

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Renovating



namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

section Core

variable {E F : Type*}

lemma symm_iter_iter (θ : Ω ≃ᵐ Ω) (k : ℕ) (a : Ω) :
    (⇑θ.symm)^[k] ((⇑θ)^[k] a) = a :=
  (Function.LeftInverse.iterate (fun x => θ.symm_apply_apply x) k) a

lemma iter_symm_iter (θ : Ω ≃ᵐ Ω) (k : ℕ) (a : Ω) :
    (⇑θ)^[k] ((⇑θ.symm)^[k] a) = a :=
  (Function.LeftInverse.iterate (fun x => θ.apply_symm_apply x) k) a

/-- the family of recurrences is "stable from `n` on" at `ω`, with common value
`W Ystar n (θ^{-n} ω)`. -/
def StableAt (θ : Ω ≃ᵐ Ω) (Yset : Set (Ω → E)) (W : (Ω → E) → ℕ → Ω → E)
    (Ystar : Ω → E) (n : ℕ) (ω : Ω) : Prop :=
  ∀ Y ∈ Yset, ∀ k : ℕ, W Y (n + k) ((⇑θ.symm)^[n + k] ω) = W Ystar n ((⇑θ.symm)^[n] ω)

lemma stableAt_val_eq {θ : Ω ≃ᵐ Ω} {Yset : Set (Ω → E)} {W : (Ω → E) → ℕ → Ω → E}
    {Ystar : Ω → E} (hYs : Ystar ∈ Yset) {n n' : ℕ} {ω : Ω}
    (h1 : StableAt θ Yset W Ystar n ω) (h2 : StableAt θ Yset W Ystar n' ω) :
    W Ystar n ((⇑θ.symm)^[n] ω) = W Ystar n' ((⇑θ.symm)^[n'] ω) := by
  have a := h1 Ystar hYs n'
  have b := h2 Ystar hYs n
  rw [add_comm] at b
  rw [← a, ← b]

open Classical in
/-- the limit random variable -/
noncomputable def limZ (θ : Ω ≃ᵐ Ω) (Yset : Set (Ω → E)) (W : (Ω → E) → ℕ → Ω → E)
    (Ystar : Ω → E) (ω : Ω) : E :=
  if h : ∃ n, StableAt θ Yset W Ystar n ω then
    W Ystar (Nat.find h) ((⇑θ.symm)^[Nat.find h] ω)
  else Ystar ω

lemma limZ_eq {θ : Ω ≃ᵐ Ω} {Yset : Set (Ω → E)} {W : (Ω → E) → ℕ → Ω → E}
    {Ystar : Ω → E} (hYs : Ystar ∈ Yset) {n : ℕ} {ω : Ω}
    (hn : StableAt θ Yset W Ystar n ω) :
    limZ θ Yset W Ystar ω = W Ystar n ((⇑θ.symm)^[n] ω) := by
  classical
  have hex : ∃ n, StableAt θ Yset W Ystar n ω := ⟨n, hn⟩
  unfold limZ
  rw [dif_pos hex]
  exact stableAt_val_eq hYs (Nat.find_spec hex) hn

lemma xi_symm_iter {θ : Ω ≃ᵐ Ω} {xi : ℕ → Ω → F} {xi0 : Ω → F}
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((⇑θ)^[n] ω)) (n : ℕ) (ω : Ω) :
    xi n ((⇑θ.symm)^[n] ω) = xi0 ω := by
  rw [hxi, iter_symm_iter]

lemma stableAt_shift {θ : Ω ≃ᵐ Ω} {h : E → F → E} {xi : ℕ → Ω → F} {xi0 : Ω → F}
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((⇑θ)^[n] ω))
    {Yset : Set (Ω → E)} {W : (Ω → E) → ℕ → Ω → E}
    (hW : ∀ Y ∈ Yset, IsRecurrentSequence h xi Y (W Y))
    {Ystar : Ω → E} (hYs : Ystar ∈ Yset) {n : ℕ} {ω : Ω}
    (hn : StableAt θ Yset W Ystar n ω) :
    StableAt θ Yset W Ystar (n + 1) (θ ω) ∧
      W Ystar (n + 1) ((⇑θ.symm)^[n + 1] (θ ω)) = h (W Ystar n ((⇑θ.symm)^[n] ω)) (xi0 ω) := by
  have hiter : ∀ j : ℕ, (⇑θ.symm)^[j + 1] (θ ω) = (⇑θ.symm)^[j] ω := by
    intro j
    rw [Function.iterate_succ_apply, θ.symm_apply_apply]
  have hval : ∀ Y ∈ Yset, ∀ k : ℕ,
      W Y (n + 1 + k) ((⇑θ.symm)^[n + 1 + k] (θ ω)) = h (W Ystar n ((⇑θ.symm)^[n] ω)) (xi0 ω) := by
    intro Y hY k
    rw [show n + 1 + k = n + k + 1 by ring, hiter, (hW Y hY).2, hn Y hY k, xi_symm_iter hxi]
  refine ⟨?_, ?_⟩
  · intro Y hY k
    rw [hval Y hY k]
    have := hval Ystar hYs 0
    simpa using this.symm
  · simpa using hval Ystar hYs 0

/-- the abstract core: from a.s. eventual stability, all three conclusions. -/
theorem core_conclusions [TopologicalSpace E]
    (P0 : Measure Ω) (θ : Ω ≃ᵐ Ω)
    (h : E → F → E) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((⇑θ)^[n] ω))
    (Yset : Set (Ω → E)) (W : (Ω → E) → ℕ → Ω → E)
    (hW : ∀ Y ∈ Yset, IsRecurrentSequence h xi Y (W Y))
    (Ystar : Ω → E) (hYs : Ystar ∈ Yset)
    (hae : ∀ᵐ ω ∂P0, ∃ n, StableAt θ Yset W Ystar n ω) :
    ∃ Z : Ω → E,
      (∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω)) ∧
      ∀ Y ∈ Yset,
        (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => W Y n ((θ.symm^[n]) ω)) atTop (𝓝 (Z ω))) ∧
        StrongBackwardsCoupling P0 θ (W Y) Z := by
  refine ⟨limZ θ Yset W Ystar, ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    obtain ⟨n, hn⟩ := hω
    obtain ⟨hs, hv⟩ := stableAt_shift hxi hW hYs hn
    rw [limZ_eq hYs hs, hv, limZ_eq hYs hn]
  · intro Y hY
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with ω hω
      obtain ⟨n, hn⟩ := hω
      rw [limZ_eq hYs hn]
      apply tendsto_atTop_of_eventually_const (i₀ := n)
      intro i hi
      obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      exact hn Y hY k
    · filter_upwards [hae] with ω hω
      obtain ⟨n, hn⟩ := hω
      refine ⟨n, fun k => ?_⟩
      rw [limZ_eq hYs hn]
      exact hn Y hY k

/-- measure lemma: measurable sets of probability tending to one inside the target set. -/
theorem ae_of_tendsto_one (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (T : Set Ω) (C : ℕ → Set Ω) (hC : ∀ n, MeasurableSet (C n))
    (hsub : ∀ n, C n ⊆ T) (hlim : Tendsto (fun n => P0 (C n)) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P0, ω ∈ T := by
  rw [ae_iff]
  have hle : ∀ n, P0 {ω | ¬ ω ∈ T} + P0 (C n) ≤ 1 := by
    intro n
    have h1 : P0 {ω | ¬ ω ∈ T} ≤ P0 (C n)ᶜ := by
      apply measure_mono
      intro ω hω hc
      exact hω (hsub n hc)
    calc P0 {ω | ¬ ω ∈ T} + P0 (C n) ≤ P0 (C n)ᶜ + P0 (C n) := add_le_add h1 le_rfl
      _ = 1 := by rw [add_comm, measure_add_measure_compl (hC n), measure_univ]
  have hlim2 : Tendsto (fun n => P0 {ω | ¬ ω ∈ T} + P0 (C n)) atTop
      (𝓝 (P0 {ω | ¬ ω ∈ T} + 1)) := hlim.const_add _
  have := le_of_tendsto' hlim2 hle
  have h2 : P0 {ω | ¬ ω ∈ T} + 1 ≤ 0 + 1 := by simpa using this
  exact le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2) zero_le'

/-- the pointwise renovation transfer. -/
lemma renov_transfer {θ : Ω ≃ᵐ Ω} {h : E → F → E} {xi : ℕ → Ω → F} {xi0 : Ω → F}
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((⇑θ)^[n] ω))
    {Y Y' : Ω → E} {WY WY' : ℕ → Ω → E}
    (hWY : IsRecurrentSequence h xi Y WY) (hWY' : IsRecurrentSequence h xi Y' WY')
    {m : ℕ} {Phi : (Fin m → F) → E} {A : ℕ → Set Ω}
    (hrenY : IsRenovating xi WY m Phi A) (hrenY' : IsRenovating xi WY' m Phi A)
    {l k n : ℕ} {ω₀ a : Ω} (hl : ω₀ ∈ A l) (ha : a ∈ A (l + k)) (hak : (⇑θ)^[k] a = ω₀)
    (hln : l ≤ n) :
    WY' (n + m + k) a = WY (n + m) ω₀ := by
  have hxs : ∀ j : ℕ, xi (j + k) a = xi j ω₀ := by
    intro j
    rw [hxi, hxi, Function.iterate_add_apply, hak]
  have hbase : WY' (l + k + m) a = WY (l + m) ω₀ := by
    rw [hrenY'.2 (l + k) a ha, hrenY.2 l ω₀ hl]
    congr 1
    funext i
    rw [show l + k + (i : ℕ) = l + i + k by ring, hxs]
  have hind : ∀ j : ℕ, WY' (l + k + m + j) a = WY (l + m + j) ω₀ := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      rw [show l + k + m + (j + 1) = (l + k + m + j) + 1 by ring,
        show l + m + (j + 1) = (l + m + j) + 1 by ring, hWY'.2, hWY.2, ih,
        show l + k + m + j = (l + m + j) + k by ring, hxs]
  obtain ⟨j, rfl⟩ : ∃ j, n = l + j := ⟨n - l, by omega⟩
  rw [show l + j + m + k = l + k + m + j by ring, show l + j + m = l + m + j by ring]
  exact hind j

end Core

section Borovkov

variable {E F : Type*}

lemma shiftImage_eq_preimage (θ : Ω ≃ᵐ Ω) (k : ℕ) (A : Set Ω) :
    shiftImage θ k A = (⇑θ.symm)^[k] ⁻¹' A := by
  ext ω
  constructor
  · rintro ⟨a, ha, rfl⟩
    show (⇑θ.symm)^[k] ((⇑θ)^[k] a) ∈ A
    rw [symm_iter_iter]; exact ha
  · intro hω
    exact ⟨(⇑θ.symm)^[k] ω, hω, iter_symm_iter θ k ω⟩

lemma measurableSet_shiftImage (θ : Ω ≃ᵐ Ω) (k : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurableSet (shiftImage θ k A) := by
  rw [shiftImage_eq_preimage]
  exact (θ.symm.measurable.iterate k) hA

theorem borovkov_core [MeasurableSpace E] [TopologicalSpace E]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : E → F → E) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (Y : Ω → E) (W : ℕ → Ω → E) (hW : IsRecurrentSequence h xi Y W)
    (m : ℕ) (Phi : (Fin m → F) → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hren : IsRenovating xi W m Phi A)
    (hcond : Tendsto
      (fun n : ℕ => P0 (⋂ k : ℕ, ⋃ l ∈ Finset.range (n + 1), A l ∩ shiftImage θ k (A (l + k))))
      atTop (𝓝 1)) :
    ∃ Z : Ω → E,
      (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => W n ((θ.symm^[n]) ω)) atTop (𝓝 (Z ω))) ∧
      (∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω)) ∧
      StrongBackwardsCoupling P0 θ W Z := by
  set Yset : Set (Ω → E) := {Y} with hYset
  set Wf : (Ω → E) → ℕ → Ω → E := fun _ => W with hWf
  have hWf' : ∀ Y' ∈ Yset, IsRecurrentSequence h xi Y' (Wf Y') := by
    intro Y' hY'
    rw [hYset, Set.mem_singleton_iff] at hY'
    subst hY'
    exact hW
  have hYs : Y ∈ Yset := Set.mem_singleton Y
  set B : ℕ → Set Ω := fun n =>
    ⋂ k : ℕ, ⋃ l ∈ Finset.range (n + 1), A l ∩ shiftImage θ k (A (l + k)) with hB
  have hBm : ∀ n, MeasurableSet (B n) := by
    intro n
    refine MeasurableSet.iInter fun k => ?_
    refine Finset.measurableSet_biUnion _ fun l _ => ?_
    exact (hA l).inter (measurableSet_shiftImage θ k (hA _))
  set C : ℕ → Set Ω := fun n => (⇑θ.symm)^[n + m] ⁻¹' B n with hC
  have hmp : MeasurePreserving θ P0 P0 := herg.toMeasurePreserving
  have hmps : MeasurePreserving θ.symm P0 P0 := MeasurePreserving.symm θ hmp
  have hCm : ∀ n, MeasurableSet (C n) := fun n =>
    (θ.symm.measurable.iterate (n + m)) (hBm n)
  have hCP : ∀ n, P0 (C n) = P0 (B n) := fun n =>
    (hmps.iterate (n + m)).measure_preimage (hBm n).nullMeasurableSet
  have hae : ∀ᵐ ω ∂P0, ∃ n, StableAt θ Yset Wf Y n ω := by
    have hlim : Tendsto (fun n => P0 (C n)) atTop (𝓝 1) := by
      simp only [hCP]; exact hcond
    apply ae_of_tendsto_one P0 _ C hCm _ hlim
    intro n ω hω
    refine ⟨n + m, ?_⟩
    intro Y' hY' k
    rw [hYset, Set.mem_singleton_iff] at hY'
    subst hY'
    have hω0 : (⇑θ.symm)^[n + m] ω ∈ B n := hω
    have hk := Set.mem_iInter.mp hω0 k
    simp only [Set.mem_iUnion, Finset.mem_range] at hk
    obtain ⟨l, hl, hlA, hlS⟩ := hk
    obtain ⟨a, ha, hak⟩ := hlS
    have hdiff : a = (⇑θ.symm)^[n + m + k] ω := by
      rw [show n + m + k = k + (n + m) by ring, Function.iterate_add_apply, ← hak,
        symm_iter_iter]
    show W (n + m + k) ((⇑θ.symm)^[n + m + k] ω) = W (n + m) ((⇑θ.symm)^[n + m] ω)
    rw [← hdiff]
    exact renov_transfer hxi hW hW hren hren hlA ha hak (by omega)
  obtain ⟨Z, hZ1, hZ2⟩ := core_conclusions P0 θ h xi xi0 hxi Yset Wf hWf' Y hYs hae
  obtain ⟨hZ3, hZ4⟩ := hZ2 Y hYs
  exact ⟨Z, hZ3, hZ1, hZ4⟩

end Borovkov

end PalmQueueing.Recurrence

open PalmQueueing.Recurrence
open MeasureTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : E → F → E) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (Y : Ω → E) (W : ℕ → Ω → E) (hW : IsRecurrentSequence h xi Y W)
    (m : ℕ) (Phi : (Fin m → F) → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hren : IsRenovating xi W m Phi A)
    (hcond : Tendsto
      (fun n : ℕ => P0 (⋂ k : ℕ, ⋃ l ∈ Finset.range (n + 1), A l ∩ shiftImage θ k (A (l + k))))
      atTop (𝓝 1)) :
    ∃ Z : Ω → E,
      (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => W n ((θ.symm^[n]) ω)) atTop (𝓝 (Z ω))) ∧
      (∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω)) ∧
      StrongBackwardsCoupling P0 θ W Z := by
  exact borovkov_core P0 θ herg h xi xi0 hxi Y W hW m Phi A hA hren hcond
