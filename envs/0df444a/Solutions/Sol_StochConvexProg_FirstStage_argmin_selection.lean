-- Prove2me | solution 1 for StochConvexProg.FirstStage.argmin_selection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:09:51.358629+00:00
-- url     : https://prove2.me/submissions/7406ab4f-8aea-4892-ba8d-a645643dd5b0

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage
import Definitions.Def_DupacovaWets_Consistency_Multifunction

open MeasureTheory Filter Topology Set


namespace SCP2Aux

variable {S : Type*} [MeasurableSpace S] {n : ℕ}

theorem T_meas (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (φ : S → (Fin n → ℝ) → ℝ) (hm : ∀ y, Measurable (fun s => φ s y))
    (hc : ∀ s, Continuous (φ s)) :
    MeasurableSet {s | ∃ y ∈ K, φ s y ≤ 0} := by
  obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
  have heq : {s | ∃ y ∈ K, φ s y ≤ 0} =
      ⋂ k : ℕ, ⋃ y ∈ D, {s | φ s y < 1 / ((k : ℝ) + 1)} := by
    ext s
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, hyK, hy⟩ k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hopen : IsOpen {z | φ s z < 1 / ((k : ℝ) + 1)} :=
        isOpen_lt (hc s) continuous_const
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (hKD hyK) _ hopen (by
        show φ s y < _; linarith)
      exact ⟨z, hz2, hz1⟩
    · intro h
      choose y hyD hy using h
      have hyK : ∀ k, y k ∈ K := fun k => hDK (hyD k)
      obtain ⟨a, haK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hyK
      refine ⟨a, haK, ?_⟩
      have h1 : Tendsto (fun k => φ s (y (ψ k))) atTop (𝓝 (φ s a)) :=
        ((hc s).tendsto a).comp hlim
      have h2 : Tendsto (fun k => 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
      exact le_of_tendsto_of_tendsto' h1 h2 (fun k => (hy (ψ k)).le)
  rw [heq]
  refine MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.biUnion hDc fun y _ => ?_
  exact measurableSet_lt (hm y) measurable_const

theorem step (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (φ ℓ : S → (Fin n → ℝ) → ℝ) (hm : ∀ y, Measurable (fun s => φ s y))
    (hc : ∀ s, Continuous (φ s)) (hmℓ : ∀ y, Measurable (fun s => ℓ s y))
    (hcℓ : ∀ s, Continuous (ℓ s)) :
    ∃ μ : S → ℝ, Measurable μ ∧ ∀ s, (∃ y ∈ K, φ s y ≤ 0) →
      (∃ y ∈ K, φ s y ≤ 0 ∧ ℓ s y = μ s) ∧ (∀ y ∈ K, φ s y ≤ 0 → μ s ≤ ℓ s y) := by
  classical
  have hmin : ∀ s, (∃ y ∈ K, φ s y ≤ 0) →
      ∃ y ∈ K ∩ {y | φ s y ≤ 0}, IsMinOn (ℓ s) (K ∩ {y | φ s y ≤ 0}) y := by
    intro s hs
    have hcpt : IsCompact (K ∩ {y | φ s y ≤ 0}) :=
      hK.inter_right (isClosed_le (hc s) continuous_const)
    obtain ⟨y, hyK, hy⟩ := hs
    exact hcpt.exists_isMinOn ⟨y, hyK, hy⟩ (hcℓ s).continuousOn
  let μ : S → ℝ := fun s => if h : (∃ y ∈ K, φ s y ≤ 0) then ℓ s (hmin s h).choose else 0
  have key : ∀ s, (∃ y ∈ K, φ s y ≤ 0) →
      (∃ y ∈ K, φ s y ≤ 0 ∧ ℓ s y = μ s) ∧ (∀ y ∈ K, φ s y ≤ 0 → μ s ≤ ℓ s y) := by
    intro s h
    have hspec := (hmin s h).choose_spec
    refine ⟨⟨(hmin s h).choose, hspec.1.1, hspec.1.2, by simp [μ, h]⟩, ?_⟩
    intro y hyK hy
    have := hspec.2 (show y ∈ K ∩ {y | φ s y ≤ 0} from ⟨hyK, hy⟩)
    simpa [μ, h] using this
  refine ⟨μ, ?_, key⟩
  apply measurable_of_Iic
  intro a
  have hT := T_meas K hK φ hm hc
  have hTa := T_meas K hK (fun s y => max (φ s y) (ℓ s y - a))
    (fun y => (hm y).max ((hmℓ y).sub measurable_const))
    (fun s => (hc s).max ((hcℓ s).sub continuous_const))
  have heq : μ ⁻¹' Iic a = ({s | ∃ y ∈ K, φ s y ≤ 0} ∩
      {s | ∃ y ∈ K, max (φ s y) (ℓ s y - a) ≤ 0}) ∪
      ({s | ∃ y ∈ K, φ s y ≤ 0}ᶜ ∩ {_s | (0 : ℝ) ≤ a}) := by
    ext s
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_setOf_eq, mem_compl_iff,
      max_le_iff, sub_nonpos]
    by_cases h : ∃ y ∈ K, φ s y ≤ 0
    · obtain ⟨⟨y, hyK, hy, hyμ⟩, hle⟩ := key s h
      constructor
      · intro hμ
        exact Or.inl ⟨h, y, hyK, hy, hyμ ▸ hμ⟩
      · rintro (⟨_, z, hzK, hz, hza⟩ | ⟨hn, _⟩)
        · exact (hle z hzK hz).trans hza
        · exact absurd h hn
    · have : μ s = 0 := by simp [μ, h]
      rw [this]
      constructor
      · intro h0; exact Or.inr ⟨h, h0⟩
      · rintro (⟨h', _⟩ | ⟨_, h0⟩)
        · exact absurd h' h
        · exact h0
  rw [heq]
  exact (hT.inter hTa).union (hT.compl.inter (MeasurableSet.const _))

theorem select (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (φ : S → (Fin n → ℝ) → ℝ) (hm : ∀ y, Measurable (fun s => φ s y))
    (hc : ∀ s, Continuous (φ s)) :
    ∃ g : S → (Fin n → ℝ), Measurable g ∧ ∀ s, (∃ y ∈ K, φ s y ≤ 0) →
      g s ∈ K ∧ φ s (g s) ≤ 0 := by
  have claim : ∀ k : ℕ, k ≤ n → ∃ ψ : S → (Fin n → ℝ) → ℝ, (∀ y, Measurable (fun s => ψ s y)) ∧
      (∀ s, Continuous (ψ s)) ∧ ∃ μ : S → (Fin n → ℝ), Measurable μ ∧
      (∀ s, (∃ y ∈ K, φ s y ≤ 0) → ∃ y ∈ K, ψ s y ≤ 0) ∧
      ∀ s y, ψ s y ≤ 0 → φ s y ≤ 0 ∧ ∀ i : Fin n, i.val < k → y i = μ s i := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨φ, hm, hc, fun _ => 0, measurable_const, fun s h => h,
        fun s y h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨ψ, hψm, hψc, μ, hμm, hT, hψ⟩ := ih (Nat.le_of_succ_le hk)
      let i₀ : Fin n := ⟨k, hk⟩
      obtain ⟨ν, hνm, hν⟩ := step K hK ψ (fun s y => y i₀) hψm hψc
        (fun y => measurable_const) (fun s => continuous_apply i₀)
      refine ⟨fun s y => max (ψ s y) |y i₀ - ν s|, ?_, ?_,
        fun s j => if j.val < k then μ s j else ν s, ?_, ?_, ?_⟩
      · intro y
        exact (hψm y).max ((measurable_const.sub hνm).abs)
      · intro s
        exact (hψc s).max (((continuous_apply i₀).sub continuous_const).abs)
      · refine measurable_pi_lambda _ fun j => ?_
        by_cases hj : j.val < k
        · simp only [hj, if_true]; exact (measurable_pi_apply j).comp hμm
        · simp only [hj, if_false]; exact hνm
      · intro s hs
        obtain ⟨⟨y, hyK, hy, hyν⟩, _⟩ := hν s (hT s hs)
        exact ⟨y, hyK, max_le hy (by simp [hyν])⟩
      · intro s y h
        have h1 : ψ s y ≤ 0 := le_trans (le_max_left _ _) h
        have h2 : |y i₀ - ν s| ≤ 0 := le_trans (le_max_right _ _) h
        have h3 : y i₀ = ν s := by
          have := abs_nonpos_iff.mp h2; linarith
        refine ⟨(hψ s y h1).1, fun i hi => ?_⟩
        by_cases hik : i.val < k
        · simp only [hik, if_true]; exact (hψ s y h1).2 i hik
        · have : i = i₀ := Fin.ext (by simp [i₀]; omega)
          subst this
          simp only [hik, if_false]; exact h3
  obtain ⟨ψ, _, _, μ, hμm, hT, hψ⟩ := claim n le_rfl
  refine ⟨μ, hμm, fun s hs => ?_⟩
  obtain ⟨y, hyK, hy⟩ := hT s hs
  have hyμ : y = μ s := funext fun i => (hψ s y hy).2 i i.isLt
  subst hyμ
  exact ⟨hyK, (hψ s _ hy).1⟩

theorem convex_slice {n₁ n₂ : ℕ} (g : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) → ℝ)
    (hg : ConvexOn ℝ univ g) (x₁ : Fin n₁ → ℝ) : ConvexOn ℝ univ (fun y => g (x₁, y)) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  have := hg.2 (mem_univ (x₁, y)) (mem_univ (x₁, z)) ha hb hab
  have e : a • (x₁, y) + b • (x₁, z) = (x₁, a • y + b • z) := by
    ext <;> simp [← add_smul, hab]
  rw [e] at this
  simpa using this

end SCP2Aux



open StochConvexProg.FirstStage in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (hC₂ : Bornology.IsBounded pr.C₂) (x₁ : Fin n₁ → ℝ) :
    (∀ s, (∃ x₂, pr.F₂ s x₁ x₂ 0 < ⊤) →
        (pr.argminSet x₁ s).Nonempty ∧ IsCompact (pr.argminSet x₁ s) ∧
          pr.argminSet x₁ s ⊆ pr.C₂) ∧
      DupacovaWets.Consistency.IsMeasurableMultifunction (fun s => pr.argminSet x₁ s) ∧
      ∃ x₂ : S → (Fin n₂ → ℝ), Measurable x₂ ∧
        ∀ s, (∃ z, pr.F₂ s x₁ z 0 < ⊤) → x₂ s ∈ pr.argminSet x₁ s := by
  classical
  have hK : IsCompact pr.C₂ := Metric.isCompact_of_isClosed_isBounded pr.C₂_closed hC₂
  have hcc : ∀ s, Continuous (fun y => pr.f₂₀ s x₁ y) := fun s =>
    continuousOn_univ.mp ((SCP2Aux.convex_slice
      (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => pr.f₂₀ s x.1 x.2) (pr.f₂₀_convex s) x₁).continuousOn
      isOpen_univ)
  have hci : ∀ i s, Continuous (fun y => pr.f₂ i s x₁ y) := fun i s =>
    continuousOn_univ.mp ((SCP2Aux.convex_slice
      (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => pr.f₂ i s x.1 x.2) (pr.f₂_convex i s) x₁).continuousOn
      isOpen_univ)
  let φ₀ : S → (Fin n₂ → ℝ) → ℝ := fun s y => ∑ i, max (pr.f₂ i s x₁ y) 0
  have hφ₀ : ∀ s y, φ₀ s y ≤ 0 ↔ ∀ i, pr.f₂ i s x₁ y ≤ 0 := by
    intro s y
    constructor
    · intro h i
      have := (Finset.single_le_sum (f := fun i => max (pr.f₂ i s x₁ y) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_univ i)).trans h
      exact (le_max_left _ _).trans this
    · intro h
      have : φ₀ s y = 0 := Finset.sum_eq_zero fun i _ => max_eq_right (h i)
      rw [this]
  have hφ₀m : ∀ y, Measurable fun s => φ₀ s y := fun y =>
    Finset.measurable_sum _ fun i _ => (pr.f₂_measurable i x₁ y).max measurable_const
  have hφ₀c : ∀ s, Continuous (φ₀ s) := fun s =>
    continuous_finset_sum _ fun i _ => (hci i s).max continuous_const
  obtain ⟨μ₀, hμ₀m, hμ₀⟩ := SCP2Aux.step pr.C₂ hK φ₀ (fun s y => pr.f₂₀ s x₁ y) hφ₀m hφ₀c
    (fun y => pr.f₂₀_measurable x₁ y) hcc
  let ψ : S → (Fin n₂ → ℝ) → ℝ := fun s y => max (φ₀ s y) |pr.f₂₀ s x₁ y - μ₀ s|
  have hψm : ∀ y, Measurable fun s => ψ s y := fun y =>
    (hφ₀m y).max (((pr.f₂₀_measurable x₁ y).sub hμ₀m).abs)
  have hψc : ∀ s, Continuous (ψ s) := fun s =>
    (hφ₀c s).max (((hcc s).sub continuous_const).abs)
  have hψ : ∀ s y, ψ s y ≤ 0 ↔ φ₀ s y ≤ 0 ∧ pr.f₂₀ s x₁ y = μ₀ s := by
    intro s y
    simp only [ψ, max_le_iff, abs_nonpos_iff, sub_eq_zero]
  obtain ⟨g, hgm, hg⟩ := SCP2Aux.select pr.C₂ hK ψ hψm hψc
  set T := {s | ∃ y ∈ pr.C₂, φ₀ s y ≤ 0} with hTdef
  have hTm : MeasurableSet T := SCP2Aux.T_meas _ hK φ₀ hφ₀m hφ₀c
  have hq_T : ∀ s ∈ T, pr.q s x₁ = (μ₀ s : EReal) := by
    intro s hs
    obtain ⟨⟨y, hyK, hy, hyμ⟩, hle⟩ := hμ₀ s hs
    simp only [Problem.q, Problem.F₂, Pi.zero_apply]
    apply le_antisymm
    · refine iInf_le_of_le y ?_
      rw [if_pos ⟨hyK, (hφ₀ s y).mp hy⟩, hyμ]
    · refine le_iInf fun z => ?_
      split_ifs with h
      · exact EReal.coe_le_coe_iff.mpr (hle z h.1 ((hφ₀ s z).mpr h.2))
      · exact le_top
  have hq_nT : ∀ s ∉ T, pr.q s x₁ = ⊤ := by
    intro s hs
    simp only [Problem.q, Problem.F₂, Pi.zero_apply]
    refine iInf_eq_top.mpr fun y => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hs ⟨y, h1, (hφ₀ s y).mpr h2⟩
  have hS' : ∀ s, (∃ x₂, pr.F₂ s x₁ x₂ 0 < ⊤) ↔ s ∈ T := by
    intro s
    constructor
    · rintro ⟨y, hy⟩
      by_contra hs
      have : pr.q s x₁ ≤ pr.F₂ s x₁ y 0 := iInf_le (fun z => pr.F₂ s x₁ z 0) y
      rw [hq_nT s hs, top_le_iff] at this
      rw [this] at hy; exact lt_irrefl _ hy
    · intro hs
      obtain ⟨⟨y, hyK, hy, _⟩, _⟩ := hμ₀ s hs
      refine ⟨y, ?_⟩
      simp only [Problem.F₂, Pi.zero_apply]
      rw [if_pos ⟨hyK, (hφ₀ s y).mp hy⟩]
      exact EReal.coe_lt_top _
  have hmem : ∀ s y, y ∈ pr.argminSet x₁ s ↔ s ∈ T ∧ y ∈ pr.C₂ ∧ ψ s y ≤ 0 := by
    intro s y
    simp only [Problem.argminSet, mem_setOf_eq]
    by_cases hs : s ∈ T
    · rw [hq_T s hs, hψ]
      simp only [Problem.F₂, Pi.zero_apply, EReal.coe_lt_top, and_true, hs, true_and]
      constructor
      · intro h
        split_ifs at h with hf
        · exact ⟨hf.1, (hφ₀ s y).mpr hf.2, EReal.coe_injective h⟩
        · exact absurd h (EReal.coe_ne_top _).symm
      · rintro ⟨h1, h2, h3⟩
        rw [if_pos ⟨h1, (hφ₀ s y).mp h2⟩, h3]
    · rw [hq_nT s hs]
      simp [hs]
  refine ⟨?_, ?_, g, hgm, ?_⟩
  · intro s hs
    have hsT := (hS' s).mp hs
    have heq : pr.argminSet x₁ s = pr.C₂ ∩ {y | ψ s y ≤ 0} := by
      ext y; rw [hmem]; simp [hsT]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨⟨y, hyK, hy, hyμ⟩, _⟩ := hμ₀ s hsT
      exact ⟨y, (hmem s y).mpr ⟨hsT, hyK, (hψ s y).mpr ⟨hy, hyμ⟩⟩⟩
    · rw [heq]; exact hK.inter_right (isClosed_le (hψc s) continuous_const)
    · intro y hy; exact ((hmem s y).mp hy).2.1
  · intro F hF
    have hKF : IsCompact (pr.C₂ ∩ F) := hK.inter_right hF
    have h2 := SCP2Aux.T_meas _ hKF ψ hψm hψc
    have heq : {s | (pr.argminSet x₁ s ∩ F).Nonempty} =
        T ∩ {s | ∃ y ∈ pr.C₂ ∩ F, ψ s y ≤ 0} := by
      ext s
      simp only [mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro ⟨y, hy, hyF⟩
        obtain ⟨hs, hyK, hψy⟩ := (hmem s y).mp hy
        exact ⟨hs, y, ⟨hyK, hyF⟩, hψy⟩
      · rintro ⟨hs, y, ⟨hyK, hyF⟩, hψy⟩
        exact ⟨y, (hmem s y).mpr ⟨hs, hyK, hψy⟩, hyF⟩
    rw [heq]; exact hTm.inter h2
  · intro s hs
    have hsT := (hS' s).mp hs
    have hs' : ∃ y ∈ pr.C₂, ψ s y ≤ 0 := by
      obtain ⟨⟨y, hyK, hy, hyμ⟩, _⟩ := hμ₀ s hsT
      exact ⟨y, hyK, (hψ s y).mpr ⟨hy, hyμ⟩⟩
    obtain ⟨h1, h2⟩ := hg s hs'
    exact (hmem s (g s)).mpr ⟨hsT, h1, h2⟩
