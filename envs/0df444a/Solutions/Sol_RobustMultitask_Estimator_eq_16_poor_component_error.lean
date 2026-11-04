-- Prove2me | solution 1 for RobustMultitask.Estimator.eq_16_poor_component_error
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:24:03.877944+00:00
-- url     : https://prove2.me/submissions/7c033398-3f14-43bc-bf38-78d59f86f7df

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment
import Theorems.Thm_RobustMultitask_Estimator_proposition_4
import Theorems.Thm_RobustMultitask_Estimator_ols_subgaussian

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
open RobustMultitask.Estimator


private theorem block_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [Countable ι] {κ : ι → Type*} [∀ i, Countable (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (hX : ∀ i j, AEMeasurable (X i j) P)
    (h : iIndepFun (fun p : (Σ i, κ i) => X p.1 p.2) P) :
    iIndepFun (fun i ω => fun j => X i j ω) P := by
  have hmY : ∀ i, AEMeasurable (fun ω => fun j => X i j ω) P :=
    fun i => aemeasurable_pi_iff.2 (hX i)
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => Measure.isProbabilityMeasure_map (hX i j)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hmY]
  have hF : AEMeasurable (fun ω (p : Σ i, κ i) => X p.1 p.2 ω) P :=
    aemeasurable_pi_iff.2 (fun p => hX p.1 p.2)
  have hcomp : (fun ω i => fun j => X i j ω)
      = (MeasurableEquiv.piCurry (fun i j => (fun (_ : κ i) => ℝ) j)) ∘
        (fun ω (p : Σ i, κ i) => X p.1 p.2 ω) := by
    ext ω i j; rfl
  have e := h.map_fun_eq_infinitePi_map₀' (fun p : (Σ i, κ i) => hX p.1 p.2)
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hF, e,
    Measure.infinitePi_map_piCurry (fun i j => P.map (X i j))]
  congr 1
  ext1 i
  have hi := h.precomp (g := fun j : κ i => (⟨i, j⟩ : Σ i, κ i)) sigma_mk_injective
  have e2 := hi.map_fun_eq_infinitePi_map₀' (fun j => hX i j)
  exact e2.symm

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (hN : 0 < N) (hd : 0 < d)
    (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (C₀ ζ η : ℝ) (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ) :
    P {ω | C₀ * d * (3 * ζ + 4 * η)
            * (⨆ ι, Real.sqrt ((σ ι : ℝ) ^ 2 / ((n ι : ℝ) * ψ) * Real.log (3 / η)))
          ≤ l1 (restrict (poorlyAligned β βdag ζ)
              (sharedEst n X (ζ + η) (fun k => response X β ε k ω) - βdag))}
      ≤ ENNReal.ofReal (3 * d * Real.exp (-((N : ℝ) * η ^ 2) / 9)) := by
  have hψ : 0 < ψ := hA1.1
  have hη2 : η ≤ 1 / 2 := by
    have : 0 < 1 / C₀ := by positivity
    linarith
  have hlog : 0 < Real.log (3 / η) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hη0]; linarith
  set L := Real.log (3 / η) with hL
  set M := ⨆ ι, Real.sqrt ((σ ι : ℝ) ^ 2 / ((n ι : ℝ) * ψ) * L) with hMdef
  -- the per-task standard deviations `√(σ_j²/(n_jψ))`
  let σ' : Fin N → ℝ≥0 := fun j => NNReal.sqrt (σ j ^ 2 / ((n j : ℝ≥0) * Real.toNNReal ψ))
  have hσ'sq : ∀ j, σ' j ^ 2 = σ j ^ 2 / ((n j : ℝ≥0) * Real.toNNReal ψ) :=
    fun j => NNReal.sq_sqrt _
  have hσ'coe : ∀ j, ((σ' j : ℝ≥0) : ℝ) = Real.sqrt ((σ j : ℝ) ^ 2 / ((n j : ℝ) * ψ)) := by
    intro j
    simp only [σ', Real.coe_sqrt, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul,
      NNReal.coe_natCast, Real.coe_toNNReal _ hψ.le]
  have hbdd : BddAbove (Set.range fun ι => Real.sqrt ((σ ι : ℝ) ^ 2 / ((n ι : ℝ) * ψ) * L)) :=
    Set.finite_range _ |>.bddAbove
  have hσ'M : ∀ j, (σ' j : ℝ) * Real.sqrt L ≤ M := by
    intro j
    rw [hσ'coe, ← Real.sqrt_mul (by positivity)]
    exact le_ciSup hbdd j
  have hMpos : 0 < M := by
    have h0 : 0 < (σ ⟨0, hN⟩ : ℝ) := by exact_mod_cast hmodel.pos_σ _
    have hn0 : (0 : ℝ) < n ⟨0, hN⟩ := by exact_mod_cast hmodel.pos_n _
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd ⟨0, hN⟩)
    apply Real.sqrt_pos.2
    positivity
  set c : ℝ := C₀ * (3 * ζ + 4 * η) * M with hc
  have hcpos : 0 < c := by
    have : 0 < C₀ := by linarith
    positivity
  -- the OLS components
  let Z : Fin d → Fin N → Ω → ℝ := fun i j ω => ols (X j) (response X β ε j ω) i
  -- block independence of the tasks' noise vectors
  have hblock : iIndepFun (fun (j : Fin N) ω => fun k => ε j k ω) P :=
    block_iIndepFun (fun j k => (hmodel.subgaussian j k).aemeasurable) hmodel.indep
  have hindZ : ∀ i (𝒥 : Finset (Fin N)),
      iIndepFun (fun j : {j : Fin N // j ∉ 𝒥} => Z i j) P := by
    intro i 𝒥
    have h1 := hblock.precomp (g := fun j : {j : Fin N // j ∉ 𝒥} => (j : Fin N))
      Subtype.val_injective
    have h2 := h1.comp (fun j e => ols (X j) (X j *ᵥ β j + e) i) (fun j => by
      unfold ols
      apply Continuous.measurable
      fun_prop)
    exact h2
  -- each poorly aligned coordinate: Proposition 4
  have hcoord : ∀ i ∈ poorlyAligned β βdag ζ,
      P {ω | c ≤ |trimmedMean (fun j => Z i j ω) (ζ + η) - βdag i|}
        ≤ ENNReal.ofReal (3 * Real.exp (-((N : ℝ) * η ^ 2) / 9)) := by
    intro i hi
    set 𝒥 := misalignedTasks β βdag i with h𝒥
    have hcard : (𝒥.card : ℝ) < ζ * N := by
      simp only [poorlyAligned, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_lt_iff₀ hNr] at hi
      exact hi
    have hsub : ∀ j ∉ 𝒥, HasSubgaussianMGF (fun ω => Z i j ω - βdag i) (σ' j ^ 2) P := by
      intro j hj
      have hβ : β j i = βdag i := by
        by_contra h
        exact hj (by simp [h𝒥, misalignedTasks, h])
      rw [hσ'sq, ← hβ]
      exact ols_subgaussian P n X β βdag s σ ε hmodel ψ hA1 j i
    have hσpos : ∀ j ∉ 𝒥, 0 < σ' j := by
      intro j _
      have h0 : 0 < (σ j : ℝ) := by exact_mod_cast hmodel.pos_σ j
      have hn0 : (0 : ℝ) < n j := by exact_mod_cast hmodel.pos_n j
      rw [← NNReal.coe_pos, hσ'coe]
      apply Real.sqrt_pos.2
      positivity
    have h4 := proposition_4 P (Z i) 𝒥 σ' (βdag i) ζ η C₀ hC₀ hζ0 hζ1 hcard hη0 hη1 hσpos hsub
      (hindZ i 𝒥)
    refine le_trans (measure_mono ?_) h4
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine le_trans ?_ hω
    have hC0 : 0 < C₀ := by linarith
    have h34 : 0 < 3 * ζ + 4 * η := by positivity
    have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hlog
    have hS : (⨆ j : {j : Fin N // j ∉ 𝒥}, (σ' j : ℝ)) * Real.sqrt L ≤ M := by
      rw [← le_div_iff₀ hsqrt]
      refine Real.iSup_le (fun j => ?_) (by positivity)
      rw [le_div_iff₀ hsqrt]
      exact hσ'M j
    calc c = C₀ * (3 * ζ + 4 * η) * M := hc
      _ ≥ C₀ * (3 * ζ + 4 * η) * ((⨆ j : {j : Fin N // j ∉ 𝒥}, (σ' j : ℝ)) * Real.sqrt L) := by
          gcongr
      _ = _ := by ring
  -- covering by the coordinate events
  have hcover : {ω | C₀ * d * (3 * ζ + 4 * η) * M
          ≤ l1 (restrict (poorlyAligned β βdag ζ)
              (sharedEst n X (ζ + η) (fun k => response X β ε k ω) - βdag))}
      ⊆ ⋃ i ∈ poorlyAligned β βdag ζ,
          {ω | c ≤ |trimmedMean (fun j => Z i j ω) (ζ + η) - βdag i|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    have hlt : l1 (restrict (poorlyAligned β βdag ζ)
        (sharedEst n X (ζ + η) (fun k => response X β ε k ω) - βdag)) < ∑ _i : Fin d, c := by
      unfold l1
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hd⟩⟩)
      intro i _
      unfold restrict
      split_ifs with hi
      · exact hcon i hi
      · simpa using hcpos
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc] at hlt
    have : (d : ℝ) * (C₀ * (3 * ζ + 4 * η) * M) = C₀ * d * (3 * ζ + 4 * η) * M := by ring
    linarith
  calc _ ≤ P (⋃ i ∈ poorlyAligned β βdag ζ,
          {ω | c ≤ |trimmedMean (fun j => Z i j ω) (ζ + η) - βdag i|}) := measure_mono hcover
    _ ≤ ∑ i ∈ poorlyAligned β βdag ζ,
          P {ω | c ≤ |trimmedMean (fun j => Z i j ω) (ζ + η) - βdag i|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ poorlyAligned β βdag ζ, ENNReal.ofReal (3 * Real.exp (-((N : ℝ) * η ^ 2) / 9)) :=
        Finset.sum_le_sum hcoord
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal (3 * Real.exp (-((N : ℝ) * η ^ 2) / 9)) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
