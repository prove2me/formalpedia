-- Prove2me | solution 1 for Plasticity.exists_separable_not_hasPlasticUnitBall
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T20:10:15.641392+00:00
-- url     : https://prove2.me/submissions/f8a17038-2abb-40ea-b537-26f7430ff56e

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Bases
import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Definitions.Def_Plasticity_C0Sum
import Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0_nat

namespace Sol_Plasticity_exists_separable_not_hasPlasticUnitBall
open Plasticity Filter Topology

theorem isClosed_c0Sum {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] : IsClosed ((c0Sum E : Submodule ℝ (lp E ⊤)) : Set (lp E ⊤)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  show Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  have hy' : Tendsto (fun i => ‖y i‖) cofinite (𝓝 0) := hy
  have h2 := (Metric.tendsto_nhds.1 hy') (ε / 2) (half_pos hε)
  filter_upwards [h2] with i hi
  have h3 : ‖x i - y i‖ ≤ ‖x - y‖ := by
    have := lp.norm_apply_le_norm (by simp : (⊤ : ENNReal) ≠ 0) (x - y) i
    simpa using this
  rw [dist_eq_norm] at hxy
  have h4 : ‖x i‖ ≤ ‖y i‖ + ‖x i - y i‖ := by
    have := norm_add_le (y i) (x i - y i); simpa [add_comm] using this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi ⊢
  linarith

theorem isClosed_c0 (Γ : Type*) : IsClosed ((c0 Γ : Submodule ℝ (Linf Γ)) : Set (Linf Γ)) := by
  have := isClosed_c0Sum (fun _ : Γ => ℝ)
  have e : ((c0 Γ : Submodule ℝ (Linf Γ)) : Set (Linf Γ)) =
      ((c0Sum (fun _ : Γ => ℝ) : Submodule ℝ (lp (fun _ : Γ => ℝ) ⊤)) : Set (Linf Γ)) := by
    ext x
    show Tendsto (⇑x) cofinite (𝓝 0) ↔ Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)
    exact tendsto_zero_iff_norm_tendsto_zero
  rw [e]; exact this

instance instC0 (Γ : Type*) : CompleteSpace (c0 Γ) := (isClosed_c0 Γ).completeSpace_coe

instance instC0Sum {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (c0Sum E) :=
  (isClosed_c0Sum E).completeSpace_coe

theorem sep_of_approx {X : Type*} [PseudoMetricSpace X] (Q : Set X) (hQ : Q.Countable)
    (h : ∀ x : X, ∀ ε > 0, ∃ q ∈ Q, dist x q < ε) : TopologicalSpace.SeparableSpace X :=
  ⟨⟨Q, hQ, fun x => Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨q, hq, h'⟩ := h x ε hε; exact ⟨q, hq, h'⟩⟩⟩

theorem single_mem_c0Sum {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (i : ℕ) (v : E i) : lp.single ⊤ i v ∈ c0Sum E := by
  show Tendsto (fun j => ‖lp.single ⊤ i v j‖) cofinite (𝓝 0)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_cofinite_ne i] with j hj
  rw [lp.single_apply_ne _ _ _ hj, norm_zero]

theorem sum_single_apply {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] {p : ENNReal} (N : ℕ) (w : (i : ℕ) → E i) (j : ℕ) :
    (∑ i : Fin N, lp.single p (i : ℕ) (w i)) j = if h : j < N then w j else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨j, h⟩ : Fin N)]
    · simp
    · intro b _ hb
      exact lp.single_apply_ne _ _ _ (fun e => hb (Fin.ext e.symm))
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    exact lp.single_apply_ne _ _ _ (by have := i.2; omega)

theorem sep_c0Sum (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (c0Sum E) := by
  choose d hd using fun i => TopologicalSpace.exists_dense_seq (E i)
  let g : (Σ N : ℕ, Fin N → ℕ) → c0Sum E := fun p =>
    ⟨∑ i : Fin p.1, lp.single ⊤ (i : ℕ) (d i (p.2 i)),
      Submodule.sum_mem _ fun i _ => single_mem_c0Sum _ _⟩
  refine sep_of_approx (Set.range g) (Set.countable_range g) ?_
  intro x ε hε
  have hx : Tendsto (fun i => ‖(x : lp E ⊤) i‖) cofinite (𝓝 0) := x.2
  have hev := (Metric.tendsto_nhds.1 hx) (ε / 2) (half_pos hε)
  rw [eventually_cofinite] at hev
  obtain ⟨N, hN⟩ := hev.bddAbove
  have hbig : ∀ j, N < j → ‖(x : lp E ⊤) j‖ < ε / 2 := by
    intro j hj
    by_contra hc
    have := hN (show j ∈ _ from by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _), not_lt] using hc)
    omega
  have hsmall : ∀ j, ∃ a, ‖(x : lp E ⊤) j - d j a‖ < ε / 2 := by
    intro j
    obtain ⟨a, ha⟩ := Metric.mem_closure_iff.1 ((hd j).closure_range ▸ Set.mem_univ ((x : lp E ⊤) j))
      (ε / 2) (half_pos hε)
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := Metric.mem_closure_iff.1
      ((hd j).closure_range ▸ Set.mem_univ ((x : lp E ⊤) j)) (ε / 2) (half_pos hε)
    exact ⟨a, by rwa [dist_eq_norm] at h⟩
  choose a ha using hsmall
  refine ⟨g ⟨N + 1, fun i => a i⟩, ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (b := ε / 2) ?_ (half_lt_self hε)
  show ‖(x : lp E ⊤) - ∑ i : Fin (N + 1), lp.single ⊤ (i : ℕ) (d i (a i))‖ ≤ ε / 2
  refine lp.norm_le_of_forall_le (half_pos hε).le fun j => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, sum_single_apply (p := ⊤) (N + 1) (fun i => d i (a i)) j]
  split_ifs with h
  · exact (ha j).le
  · rw [sub_zero]; exact (hbig j (by omega)).le

theorem sep_ell1 : TopologicalSpace.SeparableSpace (lp (fun _ : ℕ => ℝ) 1) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ℝ
  let g : (Σ N : ℕ, Fin N → ℕ) → lp (fun _ : ℕ => ℝ) 1 := fun p =>
    ∑ i : Fin p.1, lp.single 1 (i : ℕ) (d (p.2 i))
  refine sep_of_approx (Set.range g) (Set.countable_range g) ?_
  intro x ε hε
  have hs := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 1) (by simp) x).tendsto_sum_nat
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hs (ε / 2) (half_pos hε)).imp fun N h => h N le_rfl
  have hq : ∀ j, ∃ a, |x j - d a| < ε / (2 * (N + 1)) := by
    intro j
    have hpos : 0 < ε / (2 * ((N : ℝ) + 1)) := by positivity
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := Metric.mem_closure_iff.1
      ((hd).closure_range ▸ Set.mem_univ (x j)) _ hpos
    exact ⟨a, by rwa [Real.dist_eq] at h⟩
  choose a ha using hq
  refine ⟨g ⟨N, fun i => a i⟩, ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have e : x - g ⟨N, fun i => a i⟩ =
      (x - ∑ i ∈ Finset.range N, lp.single 1 i (x i)) +
        ∑ i : Fin N, lp.single (E := fun _ : ℕ => ℝ) 1 (i : ℕ) (x i - d (a i)) := by
    simp only [g, lp.single_sub, Finset.sum_sub_distrib, Finset.sum_range]
    abel
  rw [e]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  have h1 : ‖x - ∑ i ∈ Finset.range N, lp.single 1 i (x i)‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]; exact hN
  have h2 : ‖∑ i : Fin N, lp.single (E := fun _ : ℕ => ℝ) 1 (i : ℕ) (x i - d (a i))‖ ≤ ε / 2 := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i : Fin N, ‖lp.single (E := fun _ : ℕ => ℝ) 1 (i : ℕ) (x i - d (a i))‖ ≤ ε / (2 * (N + 1)) := by
      intro i
      rw [lp.norm_single (by simp), Real.norm_eq_abs]; exact (ha i).le
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  linarith

theorem sep_c0 : TopologicalSpace.SeparableSpace (c0 ℕ) := by
  haveI := sep_c0Sum (fun _ : ℕ => ℝ)
  let φ : c0Sum (fun _ : ℕ => ℝ) → c0 ℕ := fun x =>
    ⟨x.1, show Tendsto (⇑(x.1 : Linf ℕ)) cofinite (𝓝 0) from
      tendsto_zero_iff_norm_tendsto_zero.2 x.2⟩
  have hc : Continuous φ := Continuous.subtype_mk continuous_subtype_val _
  have hs : Function.Surjective φ := fun y =>
    ⟨⟨y.1, tendsto_zero_iff_norm_tendsto_zero.1 y.2⟩, rfl⟩
  exact hs.denseRange.separableSpace hc

end Sol_Plasticity_exists_separable_not_hasPlasticUnitBall

open Plasticity Sol_Plasticity_exists_separable_not_hasPlasticUnitBall in
theorem solution :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ ¬ HasPlasticUnitBall Z := by
  haveI := sep_ell1
  haveI := sep_c0
  haveI := sep_c0Sum (fun _ : ℕ => lp (fun _ : ℕ => ℝ) 1)
  haveI := sep_c0Sum (fun _ : ℕ => c0 ℕ)
  exact ⟨c0Sum (fun _ : ℕ => lp (fun _ : ℕ => ℝ) 1) × c0Sum (fun _ : ℕ => c0 ℕ), inferInstance,
    inferInstance, inferInstance, inferInstance, C0Sum.not_hasPlasticUnitBall_ell1_c0_nat⟩
