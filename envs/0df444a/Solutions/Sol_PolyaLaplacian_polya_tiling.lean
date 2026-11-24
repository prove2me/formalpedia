-- Prove2me | solution 1 for PolyaLaplacian.polya_tiling
-- status  : ACCEPTED   (disprove)
-- author  : @Secousses
-- created : 2026-11-24T23:10:02.879517+00:00
-- url     : https://prove2.me/submissions/d2dad391-8c45-4eb8-b6a4-4a4c4d69653f

import Mathlib
import Definitions.Def_PolyaLaplacian_Spectral

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open PolyaLaplacian

/-- As formalized, `dirichletEigenvalue Ω k = 0` for every `k ≥ 1`: in `ℝ`,
`⨅ (_ : finrank V = k), _` is `sInf ∅ = 0` whenever `finrank V ≠ k` (e.g. `V = ⊥`),
and every term of the outer infimum is `≥ 0`. -/
private lemma eig_zero {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : 1 ≤ k) :
    dirichletEigenvalue Ω k = 0 := by
  unfold dirichletEigenvalue
  have hnn : ∀ V : Submodule ℝ (TestFn Ω),
      0 ≤ ⨅ (_ : Module.finrank ℝ V = k),
        ⨆ (u : V) (_ : (u : TestFn Ω) ≠ 0), rayleighQuotient Ω (u : TestFn Ω) := by
    intro V
    apply Real.iInf_nonneg
    intro _
    apply Real.iSup_nonneg
    intro u
    by_cases hu : (u : TestFn Ω) = 0
    · simp [hu]
    · have : Nonempty ((u : TestFn Ω) ≠ 0) := ⟨hu⟩
      rw [ciSup_const]
      unfold rayleighQuotient dirichletEnergy l2Mass
      apply div_nonneg
      · exact setIntegral_nonneg_of_ae_restrict
          (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
      · exact integral_nonneg fun x => sq_nonneg _
  apply le_antisymm
  · refine (ciInf_le ⟨0, ?_⟩ (⊥ : Submodule ℝ (TestFn Ω))).trans ?_
    · rintro _ ⟨V, rfl⟩; exact hnn V
    · have h : Module.finrank ℝ (⊥ : Submodule ℝ (TestFn Ω)) ≠ k := by
        rw [finrank_bot]; omega
      have : IsEmpty (Module.finrank ℝ (⊥ : Submodule ℝ (TestFn Ω)) = k) := ⟨h⟩
      rw [Real.iInf_of_isEmpty]
  · exact Real.iInf_nonneg hnn

private lemma area_pos_of {s : Set (EuclideanSpace ℝ (Fin 2))} (ho : IsOpen s)
    (hne : s.Nonempty) (hb : Bornology.IsBounded s) : 0 < area s := by
  unfold area
  exact ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne

private lemma line_null (i : Fin 2) (c : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin 2) | x i = c} = 0 := by
  have hmp := PiLp.volume_preserving_ofLp (Fin 2)
  have : {x : EuclideanSpace ℝ (Fin 2) | x i = c} =
      (WithLp.ofLp) ⁻¹' ((Function.eval i : (Fin 2 → ℝ) → ℝ) ⁻¹' ({c} : Set ℝ)) := by
    ext x; simp
  rw [this, hmp.measure_preimage (measurableSet_singleton c |>.preimage (measurable_pi_apply i)).nullMeasurableSet]
  exact Measure.pi_eval_preimage_null _ (by simp)

private def sqr : Set (EuclideanSpace ℝ (Fin 2)) := {x | ∀ i, 0 < x i ∧ x i < 1}

private def vec (p : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) := !₂[(p.1 : ℝ), (p.2 : ℝ)]

private def enum : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm

private lemma int_eq_of {a b : ℤ} {s t : ℝ} (hs : 0 < s ∧ s < 1) (ht : 0 < t ∧ t < 1)
    (h : s + a = t + b) : a = b := by
  have h1 : ((a - b : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : (-1 : ℝ) < ((a - b : ℤ) : ℝ) := by push_cast; linarith
  have h1' : a - b < 1 := by exact_mod_cast h1
  have h2' : -1 < a - b := by exact_mod_cast h2
  omega

private lemma sqr_open : IsOpen sqr := by
  have : sqr = ⋂ i : Fin 2, ({x : EuclideanSpace ℝ (Fin 2) | 0 < x i} ∩ {x | x i < 1}) := by
    ext x; simp [sqr]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)

private lemma sqr_bdd : Bornology.IsBounded sqr := by
  refine Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 2) |>.subset ?_
  intro x hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' (by norm_num)]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have := hx 0; have := hx 1
  nlinarith

private lemma sqr_ne : sqr.Nonempty := ⟨!₂[1/2, 1/2], fun i => by fin_cases i <;> norm_num⟩

private lemma sqr_tile : ∃ f : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)),
      (∀ i j : ℕ, i ≠ j → Disjoint (f i '' sqr) (f j '' sqr)) ∧
      volume ((⋃ i : ℕ, f i '' sqr)ᶜ) = 0 := by
  refine ⟨fun i => IsometryEquiv.addRight (vec (enum i)), ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxy⟩
    apply hij
    apply enum.injective
    simp only [IsometryEquiv.addRight_apply] at hxy
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hxy
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hxy
    simp [vec] at h0 h1
    exact Prod.ext (int_eq_of (hx 0) (hx' 0) h0.symm) (int_eq_of (hx 1) (hx' 1) h1.symm)
  · apply measure_mono_null (t := (⋃ n : ℤ, {x : EuclideanSpace ℝ (Fin 2) | x 0 = n}) ∪
        (⋃ n : ℤ, {x : EuclideanSpace ℝ (Fin 2) | x 1 = n}))
    · intro x hx
      by_contra hc
      simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists] at hc
      apply hx
      rw [mem_iUnion]
      refine ⟨enum.symm (⌊x 0⌋, ⌊x 1⌋), x - vec (⌊x 0⌋, ⌊x 1⌋), ?_, ?_⟩
      · intro i
        have key : ∀ t : ℝ, (∀ n : ℤ, ¬ t = n) → 0 < t - ⌊t⌋ ∧ t - ⌊t⌋ < 1 := by
          intro t ht
          refine ⟨?_, by linarith [Int.lt_floor_add_one t]⟩
          rcases (Int.floor_le t).lt_or_eq with h | h
          · linarith
          · exact absurd h.symm (ht _)
        fin_cases i
        · simpa [vec] using key _ hc.1
        · simpa [vec] using key _ hc.2
      · simp
    · exact measure_union_null (measure_iUnion_null fun n => line_null 0 n)
        (measure_iUnion_null fun n => line_null 1 n)

theorem solution : ¬ (∀ (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (htile : ∃ f : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)),
      (∀ i j : ℕ, i ≠ j → Disjoint (f i '' Ω) (f j '' Ω)) ∧
      volume ((⋃ i : ℕ, f i '' Ω)ᶜ) = 0),
    ∀ k : ℕ, 1 ≤ k → dirichletEigenvalue Ω k ≥ 4 * Real.pi * (k : ℝ) / area Ω) := by
  intro h
  have h1 := h sqr sqr_open sqr_bdd sqr_ne sqr_tile 1 le_rfl
  rw [eig_zero _ 1 le_rfl] at h1
  have : 0 < 4 * Real.pi * ((1 : ℕ) : ℝ) / area sqr :=
    div_pos (by positivity) (area_pos_of sqr_open sqr_ne sqr_bdd)
  linarith
