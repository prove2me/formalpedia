-- Prove2me | solution 1 for StochConvexProg.FirstStage.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:11:09.562509+00:00
-- url     : https://prove2.me/submissions/f03c5203-3347-4c01-abd6-4c1fd24993ab

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage

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
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    ∀ x₁ : Fin n₁ → ℝ, Measurable (fun s => pr.q s x₁) := by
  classical
  intro x₁
  have hKN : ∀ N : ℕ, IsCompact (pr.C₂ ∩ Metric.closedBall (0 : Fin n₂ → ℝ) N) := fun N =>
    (isCompact_closedBall _ _).inter_left pr.C₂_closed
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
  have hF₂ : ∀ s y, pr.F₂ s x₁ y 0 =
      if y ∈ pr.C₂ ∧ φ₀ s y ≤ 0 then ((pr.f₂₀ s x₁ y : ℝ) : EReal) else ⊤ := by
    intro s y
    simp only [Problem.F₂, Pi.zero_apply, hφ₀]
  apply measurable_of_Iio
  intro x
  induction x using EReal.rec with
  | bot => simp
  | top =>
    have heq : (fun s => pr.q s x₁) ⁻¹' Iio ⊤ =
        ⋃ N : ℕ, {s | ∃ y ∈ pr.C₂ ∩ Metric.closedBall (0 : Fin n₂ → ℝ) N, φ₀ s y ≤ 0} := by
      ext s
      simp only [mem_preimage, mem_Iio, Problem.q, iInf_lt_iff, mem_iUnion, mem_setOf_eq,
        mem_inter_iff, Metric.mem_closedBall, dist_zero_right, hF₂]
      constructor
      · rintro ⟨y, hy⟩
        split_ifs at hy with h
        · obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
          exact ⟨N, y, ⟨h.1, hN⟩, h.2⟩
        · exact absurd hy (lt_irrefl _)
      · rintro ⟨N, y, ⟨hy1, _⟩, hy2⟩
        exact ⟨y, by rw [if_pos ⟨hy1, hy2⟩]; exact EReal.coe_lt_top _⟩
    rw [heq]
    exact MeasurableSet.iUnion fun N => SCP2Aux.T_meas _ (hKN N) φ₀ hφ₀m hφ₀c
  | coe r =>
    have heq : (fun s => pr.q s x₁) ⁻¹' Iio (r : EReal) =
        ⋃ N : ℕ, ⋃ k : ℕ, {s | ∃ y ∈ pr.C₂ ∩ Metric.closedBall (0 : Fin n₂ → ℝ) N,
          max (φ₀ s y) (pr.f₂₀ s x₁ y - r + 1 / ((k : ℝ) + 1)) ≤ 0} := by
      ext s
      simp only [mem_preimage, mem_Iio, Problem.q, iInf_lt_iff, mem_iUnion, mem_setOf_eq,
        mem_inter_iff, Metric.mem_closedBall, dist_zero_right, hF₂, max_le_iff]
      constructor
      · rintro ⟨y, hy⟩
        split_ifs at hy with h
        · have hlt : pr.f₂₀ s x₁ y < r := EReal.coe_lt_coe_iff.mp hy
          obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
          exact ⟨N, k, y, ⟨h.1, hN⟩, h.2, by linarith⟩
        · exact absurd hy (not_lt.mpr le_top)
      · rintro ⟨N, k, y, ⟨hy1, _⟩, hy2, hy3⟩
        refine ⟨y, ?_⟩
        rw [if_pos ⟨hy1, hy2⟩]
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
    rw [heq]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun k =>
      SCP2Aux.T_meas _ (hKN N) _
        (fun y => (hφ₀m y).max (((pr.f₂₀_measurable x₁ y).sub measurable_const).add
          measurable_const))
        (fun s => (hφ₀c s).max (((hcc s).sub continuous_const).add continuous_const))
