-- Prove2me | solution 1 for StochConvexProg.FirstStage.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:06:11.302202+00:00
-- url     : https://prove2.me/submissions/e01d2ab6-224a-4d85-8482-ffec78d9226c

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage
import Theorems.Thm_StochConvexProg_FirstStage_eq_3_5_3_6

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

end SCP2Aux


namespace SCP2Aux

theorem cvx_upper {n : ℕ} (u : (Fin n → ℝ) → ℝ) (hu : ConvexOn ℝ univ u) (R : ℝ) (hR : 0 ≤ R)
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ R) :
    u y ≤ |u 0| + ∑ i, (|u (Pi.single i ((n : ℝ) * R + 1))| +
      |u (Pi.single i (-((n : ℝ) * R + 1)))|) := by
  classical
  set M : ℝ := (n : ℝ) * R + 1 with hM
  have hMpos : 0 < M := by positivity
  have hyi : ∀ i, |y i| ≤ R := fun i => (norm_le_pi_norm y i).trans hy
  have hsum : ∑ i, |y i| < M := by
    calc ∑ i, |y i| ≤ ∑ _i : Fin n, R := Finset.sum_le_sum fun i _ => hyi i
      _ = n * R := by simp
      _ < M := by linarith
  let w : Option (Fin n) → ℝ := fun o => match o with
    | none => 1 - ∑ i, |y i| / M
    | some i => |y i| / M
  let p : Option (Fin n) → (Fin n → ℝ) := fun o => match o with
    | none => 0
    | some i => Pi.single i (if 0 ≤ y i then M else -M)
  have hsdiv : ∑ i, |y i| / M ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hMpos]; exact hsum.le
  have hw0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w o := by
    intro o _
    cases o with
    | none => simp only [w]; linarith
    | some i => simp only [w]; positivity
  have hw1 : ∑ o, w o = 1 := by
    rw [Fintype.sum_option]; simp only [w]; ring
  have hwp : ∑ o, w o • p o = y := by
    rw [Fintype.sum_option]
    simp only [w, p, smul_zero, zero_add]
    conv_rhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul]
    congr 1
    split_ifs with h
    · rw [abs_of_nonneg h, smul_eq_mul]; field_simp
    · rw [abs_of_neg (lt_of_not_ge h), smul_eq_mul]; field_simp
  have hJ := hu.map_sum_le hw0 hw1 (fun o _ => mem_univ (p o))
  rw [hwp] at hJ
  refine hJ.trans ?_
  rw [Fintype.sum_option]
  simp only [w, p, smul_eq_mul]
  have hA : (1 - ∑ i, |y i| / M) * u 0 ≤ |u 0| := by
    have h0 : 0 ≤ 1 - ∑ i, |y i| / M := by linarith
    have h1 : 1 - ∑ i, |y i| / M ≤ 1 := by
      have : 0 ≤ ∑ i, |y i| / M := Finset.sum_nonneg fun i _ => by positivity
      linarith
    calc (1 - ∑ i, |y i| / M) * u 0 ≤ (1 - ∑ i, |y i| / M) * |u 0| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 1 * |u 0| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |u 0| := one_mul _
  have hB : ∀ i, |y i| / M * u (Pi.single i (if 0 ≤ y i then M else -M)) ≤
      |u (Pi.single i M)| + |u (Pi.single i (-M))| := by
    intro i
    have hwi0 : 0 ≤ |y i| / M := by positivity
    have hwi1 : |y i| / M ≤ 1 := by
      rw [div_le_one hMpos]
      exact (Finset.single_le_sum (f := fun i => |y i|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)).trans hsum.le
    have hb : |u (Pi.single i (if 0 ≤ y i then M else -M))| ≤
        |u (Pi.single i M)| + |u (Pi.single i (-M))| := by
      split_ifs
      · linarith [abs_nonneg (u (Pi.single i (-M)))]
      · linarith [abs_nonneg (u (Pi.single i M))]
    calc |y i| / M * u (Pi.single i (if 0 ≤ y i then M else -M))
        ≤ |y i| / M * |u (Pi.single i (if 0 ≤ y i then M else -M))| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hwi0
      _ ≤ 1 * |u (Pi.single i (if 0 ≤ y i then M else -M))| :=
          mul_le_mul_of_nonneg_right hwi1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb
  exact add_le_add hA (Finset.sum_le_sum fun i _ => hB i)

theorem cvx_abs {n : ℕ} (u : (Fin n → ℝ) → ℝ) (hu : ConvexOn ℝ univ u) (R : ℝ) (hR : 0 ≤ R)
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ R) :
    |u y| ≤ 3 * (|u 0| + ∑ i, (|u (Pi.single i ((n : ℝ) * R + 1))| +
      |u (Pi.single i (-((n : ℝ) * R + 1)))|)) := by
  set B := |u 0| + ∑ i, (|u (Pi.single i ((n : ℝ) * R + 1))| +
      |u (Pi.single i (-((n : ℝ) * R + 1)))|) with hBdef
  have h1 := cvx_upper u hu R hR y hy
  have h2 := cvx_upper u hu R hR (-y) (by rwa [norm_neg])
  have hB0 : |u 0| ≤ B := by
    have : 0 ≤ ∑ i, (|u (Pi.single i ((n : ℝ) * R + 1))| +
      |u (Pi.single i (-((n : ℝ) * R + 1)))|) := Finset.sum_nonneg fun i _ => by positivity
    linarith
  -- convexity at midpoint: u 0 ≤ (u y + u (-y)) / 2
  have hmid : u 0 ≤ (1/2 : ℝ) * u y + (1/2 : ℝ) * u (-y) := by
    have := hu.2 (mem_univ y) (mem_univ (-y)) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [smul_neg] using this
  have h0 := neg_abs_le (u 0)
  rw [abs_le]
  constructor <;> linarith

end SCP2Aux


namespace SCP2Aux
open StochConvexProg.FirstStage

theorem convex_slice {n₁ n₂ : ℕ} (g : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) → ℝ)
    (hg : ConvexOn ℝ univ g) (x₁ : Fin n₁ → ℝ) : ConvexOn ℝ univ (fun y => g (x₁, y)) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  have := hg.2 (mem_univ (x₁, y)) (mem_univ (x₁, z)) ha hb hab
  have e : a • (x₁, y) + b • (x₁, z) = (x₁, a • y + b • z) := by
    ext <;> simp [← add_smul, hab]
  rw [e] at this
  simpa using this

theorem attain {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (hC₂ : Bornology.IsBounded pr.C₂)
    (x₁ : Fin n₁ → ℝ) (hj : pr.j x₁ < ⊤) :
    ∃ x₂ : Lp (Fin n₂ → ℝ) ⊤ σ, pr.f (x₁, x₂) = pr.j x₁ := by
  classical
  have hK : IsCompact pr.C₂ := Metric.isCompact_of_isClosed_isBounded pr.C₂_closed hC₂
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hC₂
  set R := max R₀ 0 with hRdef
  have hR : ∀ y ∈ pr.C₂, ‖y‖ ≤ R := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  have hcv : ∀ s, ConvexOn ℝ univ (fun y => pr.f₂₀ s x₁ y) := fun s =>
    convex_slice (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => pr.f₂₀ s x.1 x.2) (pr.f₂₀_convex s) x₁
  have hcc : ∀ s, Continuous (fun y => pr.f₂₀ s x₁ y) := fun s =>
    continuousOn_univ.mp ((hcv s).continuousOn isOpen_univ)
  have hci : ∀ i s, Continuous (fun y => pr.f₂ i s x₁ y) := fun i s =>
    continuousOn_univ.mp ((convex_slice
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
  obtain ⟨μ₀, hμ₀m, hμ₀⟩ := step pr.C₂ hK φ₀ (fun s y => pr.f₂₀ s x₁ y) hφ₀m hφ₀c
    (fun y => pr.f₂₀_measurable x₁ y) hcc
  obtain ⟨g, hgm, hg⟩ := select pr.C₂ hK (fun s y => max (φ₀ s y) |pr.f₂₀ s x₁ y - μ₀ s|)
    (fun y => (hφ₀m y).max (((pr.f₂₀_measurable x₁ y).sub hμ₀m).abs))
    (fun s => (hφ₀c s).max (((hcc s).sub continuous_const).abs))
  set T := {s | ∃ y ∈ pr.C₂, φ₀ s y ≤ 0} with hTdef
  have hTm : MeasurableSet T := T_meas _ hK φ₀ hφ₀m hφ₀c
  have hgT : ∀ s ∈ T, g s ∈ pr.C₂ ∧ (∀ i, pr.f₂ i s x₁ (g s) ≤ 0) ∧
      pr.f₂₀ s x₁ (g s) = μ₀ s := by
    intro s hs
    have hs' : ∃ y ∈ pr.C₂, max (φ₀ s y) |pr.f₂₀ s x₁ y - μ₀ s| ≤ 0 := by
      obtain ⟨⟨y, hyK, hy, hyμ⟩, _⟩ := hμ₀ s hs
      exact ⟨y, hyK, max_le hy (by simp [hyμ])⟩
    obtain ⟨h1, h2⟩ := hg s hs'
    have a1 : φ₀ s (g s) ≤ 0 := le_trans (le_max_left _ _) h2
    have a2 : |pr.f₂₀ s x₁ (g s) - μ₀ s| ≤ 0 := le_trans (le_max_right _ _) h2
    refine ⟨h1, (hφ₀ s _).mp a1, ?_⟩
    have := abs_nonpos_iff.mp a2; linarith
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
  -- first-stage data
  have hF₁' : x₁ ∈ pr.C₁ ∧ ∀ i, pr.f₁ i x₁ ≤ 0 := by
    by_contra h
    have : pr.F₁ x₁ 0 = ⊤ := by
      simp only [Problem.F₁, Pi.zero_apply]; rw [if_neg h]
    have hj' : pr.j x₁ = ⊤ := by
      simp only [Problem.j, this, lt_self_iff_false, if_false]
    rw [hj'] at hj; exact lt_irrefl _ hj
  have hF₁val : pr.F₁ x₁ 0 = (pr.f₁₀ x₁ : EReal) := by
    simp only [Problem.F₁, Pi.zero_apply]; rw [if_pos hF₁']
  have hj_eq : pr.j x₁ = (pr.f₁₀ x₁ : EReal) +
      DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁) := by
    simp only [Problem.j, hF₁val, EReal.coe_lt_top, if_true]
  have hlin : ∫⁻ s, (pr.q s x₁).toENNReal ∂σ ≠ ⊤ := by
    intro h
    have : DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁) = ⊤ := by
      simp only [DupacovaWets.Consistency.expect]; rw [if_pos h]
    rw [hj_eq, this, EReal.coe_add_top] at hj
    exact lt_irrefl _ hj
  have hTae : σ Tᶜ = 0 := by
    by_contra h0
    refine hlin (eq_top_iff.mpr ?_)
    calc (⊤ : ENNReal) = ∫⁻ s in Tᶜ, ⊤ ∂σ := by rw [setLIntegral_const, ENNReal.top_mul h0]
      _ = ∫⁻ s in Tᶜ, (pr.q s x₁).toENNReal ∂σ :=
          setLIntegral_congr_fun hTm.compl (fun s hs => by
            rw [hq_nT s hs]; rfl)
      _ ≤ ∫⁻ s, (pr.q s x₁).toENNReal ∂σ := setLIntegral_le_lintegral _ _
  have hT : ∀ᵐ s ∂σ, s ∈ T := mem_ae_iff.mpr hTae
  -- integrability
  have hU : Integrable (fun s => |pr.f₂₀ s x₁ 0| + ∑ i, (|pr.f₂₀ s x₁ (Pi.single i ((n₂ : ℝ) * R + 1))| +
      |pr.f₂₀ s x₁ (Pi.single i (-((n₂ : ℝ) * R + 1)))|)) σ :=
    ((pr.f₂₀_integrable x₁ 0).abs).add (integrable_finset_sum _ fun i _ =>
      ((pr.f₂₀_integrable _ _).abs).add ((pr.f₂₀_integrable _ _).abs))
  have hμ₀int : Integrable μ₀ σ := by
    refine (hU.const_mul 3).mono' hμ₀m.aestronglyMeasurable ?_
    filter_upwards [hT] with s hs
    rw [Real.norm_eq_abs, ← (hgT s hs).2.2]
    exact cvx_abs _ (hcv s) R (le_max_right _ _) _ (hR _ (hgT s hs).1)
  have hgL : MemLp g ⊤ σ := memLp_top_of_bound hgm.aestronglyMeasurable R (by
    filter_upwards [hT] with s hs; exact hR _ (hgT s hs).1)
  refine ⟨hgL.toLp g, ?_⟩
  have hfeas : pr.Feasible (x₁, hgL.toLp g) 0 := by
    refine ⟨hF₁'.1, fun i => by simpa using hF₁'.2 i, ?_⟩
    filter_upwards [hgL.coeFn_toLp, Lp.coeFn_zero (E := Fin m₂ → ℝ) (p := ⊤) (μ := σ), hT]
      with s h1 h2 hs
    show (hgL.toLp g) s ∈ _ ∧ _
    rw [h1]
    exact ⟨(hgT s hs).1, fun i => by simpa using (hgT s hs).2.1 i⟩
  have hint : ∫ s, pr.f₂₀ s x₁ ((hgL.toLp g) s) ∂σ = ∫ s, μ₀ s ∂σ := by
    refine integral_congr_ae ?_
    filter_upwards [hgL.coeFn_toLp, hT] with s h1 hs
    rw [h1, (hgT s hs).2.2]
  have hf : pr.f (x₁, hgL.toLp g) = ((pr.f₁₀ x₁ + ∫ s, μ₀ s ∂σ : ℝ) : EReal) := by
    simp only [Problem.f, Problem.F]
    rw [if_pos hfeas]
    exact congrArg (fun t : ℝ => ((pr.f₁₀ x₁ + t : ℝ) : EReal)) hint
  have e1 : ∫⁻ s, (pr.q s x₁).toENNReal ∂σ = ∫⁻ s, ENNReal.ofReal (μ₀ s) ∂σ :=
    lintegral_congr_ae (by filter_upwards [hT] with s hs; rw [hq_T s hs]; rfl)
  have e2 : ∫⁻ s, (-pr.q s x₁).toENNReal ∂σ = ∫⁻ s, ENNReal.ofReal (-μ₀ s) ∂σ :=
    lintegral_congr_ae (by filter_upwards [hT] with s hs; rw [hq_T s hs, ← EReal.coe_neg]; rfl)
  have h1' : ∫⁻ s, ENNReal.ofReal (μ₀ s) ∂σ ≠ ⊤ := hμ₀int.lintegral_lt_top.ne
  have h2' : ∫⁻ s, ENNReal.ofReal (-μ₀ s) ∂σ ≠ ⊤ := hμ₀int.neg.lintegral_lt_top.ne
  have hexp : DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁) =
      ((∫ s, μ₀ s ∂σ : ℝ) : EReal) := by
    simp only [DupacovaWets.Consistency.expect]
    rw [e1, e2, if_neg h1', integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ₀int,
      EReal.coe_sub, EReal.coe_ennreal_toReal h1', EReal.coe_ennreal_toReal h2']
  rw [hf, hj_eq, hexp, EReal.coe_add]

end SCP2Aux

open StochConvexProg.FirstStage in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (hC₂ : Bornology.IsBounded pr.C₂) :
    (∀ x₁, pr.j x₁ = pr.J x₁) ∧ pr.infQ = pr.infP ∧
      (∀ x₁, (∀ x₁', pr.j x₁ ≤ pr.j x₁') ↔ (∀ x₁', pr.J x₁ ≤ pr.J x₁')) ∧
      (∀ x₁, ∃ x₂ : Lp (Fin n₂ → ℝ) ⊤ σ, pr.f (x₁, x₂) = pr.J x₁) := by
  have h35 := (StochConvexProg.FirstStage.eq_3_5_3_6 pr).1
  have hjJ : ∀ x₁, pr.j x₁ = pr.J x₁ := by
    intro x₁
    apply le_antisymm (le_iInf fun x₂ => h35 x₁ x₂)
    by_cases h : pr.j x₁ < ⊤
    · obtain ⟨x₂, hx₂⟩ := SCP2Aux.attain pr hC₂ x₁ h
      rw [← hx₂]
      exact iInf_le (fun x₂ : Lp (Fin n₂ → ℝ) ⊤ σ => pr.f (x₁, x₂)) x₂
    · rw [not_lt, top_le_iff] at h
      rw [h]; exact le_top
  refine ⟨hjJ, ?_, ?_, ?_⟩
  · simp only [Problem.infQ, Problem.infP, hjJ, Problem.J]
    rw [iInf_prod]
  · intro x₁; simp only [hjJ]
  · intro x₁
    by_cases h : pr.j x₁ < ⊤
    · obtain ⟨x₂, hx₂⟩ := SCP2Aux.attain pr hC₂ x₁ h
      exact ⟨x₂, hx₂.trans (hjJ x₁)⟩
    · refine ⟨0, ?_⟩
      have hJ : pr.J x₁ = ⊤ := (hjJ x₁) ▸ (top_le_iff.mp (not_lt.mp h))
      rw [hJ]
      have : pr.J x₁ ≤ pr.f (x₁, 0) :=
        iInf_le (fun x₂ : Lp (Fin n₂ → ℝ) ⊤ σ => pr.f (x₁, x₂)) 0
      rw [hJ] at this
      exact top_le_iff.mp this
