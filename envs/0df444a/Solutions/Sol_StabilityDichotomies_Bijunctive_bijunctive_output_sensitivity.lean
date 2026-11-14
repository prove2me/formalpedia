-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_output_sensitivity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:53:27.311859+00:00
-- url     : https://prove2.me/submissions/b7d014fb-38a1-4dd4-ab8a-9f55d0a91688
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_deletion_graph_feasibility_cost_split
import Theorems.Thm_StabilityDichotomies_Bijunctive_total_graph_deletion_bit_change_probabilities_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_total_feasibility_root_deletion_change_probability_bound
import Theorems.Thm_StabilityDichotomies_Solvability_delete_equivalence_at_original_index
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem sum_over_occurrences {Γ : Language} {V : Type} (I : Instance Γ V)
    (f : Constraint Γ V → ℝ) :
    (I.constraints.map f).sum = ∑ i : Fin I.constraints.card, f (occurrenceAt I i) := by
  have hl : List.ofFn (occurrenceAt I) = I.constraints.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [occurrenceAt]
  calc
    _ = (I.constraints.toList.map f).sum := by simp
    _ = ((List.ofFn (occurrenceAt I)).map f).sum := by rw [hl]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem conditional_bijunctive_sensitivity_concrete_bound (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ) (hLaw : BijunctiveOutputLaw Γ rep ε A)
    (V : Type) [Fintype V] [Nonempty V] (I : Instance Γ V) (hI : Satisfiable I) :
    averageSensitivity A I ≤ (maxArity Γ : ℝ) *
      (((Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε) +
        (2 / ε) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  classical
  let Ω := (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let μ : Measure Ω := bijunctiveSeedMeasure rep I ε
  let G := fun (j : Fin I.constraints.card) (z : Ω) =>
    thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
  let F := fun z : Ω => thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
  let Fminus := fun (j : Fin I.constraints.card) (z : Ω) =>
    thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
  let mid := fun j z v => decide (literalScore rep (G j z) (F z) z.2.2 (v,false) < literalScore rep (G j z) (F z) z.2.2 (v,true))
  let last := fun j z v => decide (literalScore rep (G j z) (Fminus j z) z.2.2 (v,false) < literalScore rep (G j z) (Fminus j z) z.2.2 (v,true))
  let X : Fin I.constraints.card → ℝ := fun j => ∑ v : V,
    (μ {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid j z v}).toReal
  let Y : Fin I.constraints.card → ℝ := fun j => ∑ v : V, (μ {z | mid j z v ≠ last j z v}).toReal
  let L : ℝ := Real.log (Fintype.card (Literal V)) + 1
  let H : ℝ := harmonic (Fintype.card (Literal V))
  let r : ℝ := maxArity Γ
  let N : ℝ := I.constraints.card
  have hβ : 0 < bijunctiveRate rep ε := by
    unfold bijunctiveRate
    apply div_pos hε
    have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  have hL : 0 ≤ L := by
    have hn : (1 : ℝ) ≤ Fintype.card (Literal V) := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Literal V))
    have := Real.log_nonneg hn
    dsimp [L]; linarith
  have hH : 0 ≤ H := by
    dsimp [H]
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hB : 0 ≤ L / bijunctiveRate rep ε + (2 / ε) * H := by positivity
  by_cases hzero : I.constraints = 0
  · simp only [averageSensitivity, hzero, ↓reduceIte]
    exact mul_nonneg hr hB
  · have hN : 0 < N := by
      dsimp [N]
      exact_mod_cast Multiset.card_pos.mpr hzero
    have hpoint (j : Fin I.constraints.card) :
        wasserstein (A V I) (A V (I.delete (occurrenceAt I j))) ≤ X j + Y j := by
      obtain ⟨e,hej,he⟩ := delete_equivalence_at_original_index I j
      exact bijunctive_deletion_graph_feasibility_cost_split rep I hI j ε hε A hLaw e hej he
    have hsum : (I.constraints.map fun c => wasserstein (A V I) (A V (I.delete c))).sum ≤
        (∑ j, X j) + (∑ j, Y j) := by
      rw [sum_over_occurrences]
      calc
        _ ≤ ∑ j, (X j + Y j) := Finset.sum_le_sum (fun j _ => hpoint j)
        _ = _ := Finset.sum_add_distrib
    have hX : (∑ j, X j) ≤ (r * N) * (L / bijunctiveRate rep ε) := by
      convert total_graph_deletion_bit_change_probabilities_bound rep I hI ε hε using 1 <;> simp [r,N,L,Nat.cast_mul]
    have hY : (∑ j, Y j) ≤ (2 / ε) * ((r * N) * H) := by
      convert total_feasibility_root_deletion_change_probability_bound rep I hI ε hε hε1 using 1 <;> simp [r,N,H,Nat.cast_mul]
    unfold averageSensitivity
    simp only [hzero, ↓reduceIte]
    change _ / N ≤ _
    apply (div_le_iff₀ hN).2
    have hs : _ := hsum.trans (add_le_add hX hY)
    nlinarith

theorem solution (Γ : Language) (rep : TwoCNFRepresentation Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Solver Γ, BijunctiveOutputLaw Γ rep ε A →
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  classical
  let r : ℝ := maxArity Γ
  let b : ℝ := rep.clauseBound
  let K : ℝ := 2 + (Real.log 2)⁻¹
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hb : 0 < b := by dsimp [b]; exact_mod_cast rep.clauseBound_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(r+1) * (2*(b+1)) * K, by positivity, ?_⟩
  intro ε hε hε1 A hLaw V _ I hI hn
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let n : ℝ := Fintype.card V
  let L : ℝ := Real.log (Fintype.card (Literal V)) + 1
  let H : ℝ := harmonic (Fintype.card (Literal V))
  have hn2 : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hnpos : 0 < n := by linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hloginv : 1 ≤ (Real.log 2)⁻¹ * Real.log n := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ (Real.log 2)⁻¹ * Real.log n := mul_le_mul_of_nonneg_left hlogn (by positivity)
  have hL : L = Real.log n + Real.log 2 + 1 := by
    dsimp [L,n,Literal]
    rw [Fintype.card_prod]
    norm_num
    rw [Real.log_mul (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
  have hLbound : L ≤ K * Real.log n := by
    rw [hL]
    dsimp [K]
    nlinarith
  have hLnonneg : 0 ≤ L := by rw [hL]; linarith
  have hHL : H ≤ L := by
    have hh := harmonic_le_one_add_log (Fintype.card (Literal V))
    dsimp [H,L]
    linarith
  have hrate : bijunctiveRate rep ε = ε / (2*b) := by rfl
  have hdiv : L / bijunctiveRate rep ε = (2*b / ε) * L := by
    rw [hrate]
    field_simp
  have hterm : L / bijunctiveRate rep ε + (2 / ε) * H ≤
      (2*(b+1)*ε⁻¹) * L := by
    rw [hdiv]
    calc
      _ ≤ (2*b / ε) * L + (2 / ε) * L := by gcongr
      _ = _ := by ring
  have hcoef : 0 ≤ 2*(b+1)*ε⁻¹ := by positivity
  have hconcrete := conditional_bijunctive_sensitivity_concrete_bound Γ rep ε hε hε1 A hLaw V I hI
  change averageSensitivity A I ≤ r * (L / bijunctiveRate rep ε + (2 / ε) * H) at hconcrete
  calc
    averageSensitivity A I ≤ r * (L / bijunctiveRate rep ε + (2 / ε) * H) := hconcrete
    _ ≤ r * ((2*(b+1)*ε⁻¹) * L) := mul_le_mul_of_nonneg_left hterm hr
    _ ≤ r * ((2*(b+1)*ε⁻¹) * (K * Real.log n)) := by
      gcongr
    _ ≤ (r+1) * ((2*(b+1)*ε⁻¹) * (K * Real.log n)) := by
      gcongr
      linarith
    _ = (r+1) * (2*(b+1)) * K * ε⁻¹ * Real.log n := by ring
