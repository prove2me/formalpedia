-- Prove2me | solution 1 for TopDownParity1043.Main.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:33:59.225314+00:00
-- url     : https://prove2.me/submissions/09b27a1e-f5b3-41bf-8b4a-3f6a0c09196e

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
import Definitions.Def_TopDownParity1043_Main_HarmonicMean
import Theorems.Thm_TopDownParity1043_Main_corollary_1

set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped NNReal ENNReal
open TopDownParity1043.Main

private noncomputable def wordEquiv {V W : Type} (e : V ≃ W) :
    (V → Bool) ≃ (W → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)

private theorem project_wordEquiv {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (R : Finset V) (x : V → Bool) :
    project (R.map e.toEmbedding) (wordEquiv e x) =
      wordEquiv (Finset.equivMap e.toEmbedding R) (project R x) := by
  classical
  apply (wordEquiv (Finset.equivMap e.toEmbedding R)).symm.injective
  apply funext
  intro i
  simp [wordEquiv, project, Equiv.arrowCongr]

private theorem conditional_relabel {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (R : Finset V)
    (f : (V → Bool) → ℝ≥0) (z : R → Bool) :
    conditionalMean (fun y => f ((wordEquiv e).symm y)) (R.map e.toEmbedding)
        (wordEquiv (Finset.equivMap e.toEmbedding R) z) = conditionalMean f R z := by
  classical
  unfold conditionalMean
  rw [← (wordEquiv e).sum_comp]
  simp only [Finset.card_map, ← Fintype.card_congr e, Equiv.symm_apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [project_wordEquiv]
  simp

private theorem harmonic_relabel {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (R : Finset V)
    (f : (V → Bool) → ℝ≥0) :
    harmonicMean (fun y => f ((wordEquiv e).symm y)) (R.map e.toEmbedding) =
      harmonicMean f R := by
  classical
  unfold harmonicMean
  rw [← (wordEquiv (Finset.equivMap e.toEmbedding R)).sum_comp]
  simp only [Finset.card_map, conditional_relabel]

private def someEmb (V : Type) : V ↪ Option V := ⟨some, Option.some_injective V⟩

private def joinWord {V : Type} (b : Bool) (x : V → Bool) : Option V → Bool :=
  fun o => Option.casesOn o b x

private theorem project_join {V : Type} [Fintype V] [DecidableEq V]
    (R : Finset V) (b : Bool) (x : V → Bool) :
    project (R.map (someEmb V)) (joinWord b x) =
      wordEquiv (Finset.equivMap (someEmb V) R) (project R x) := by
  classical
  apply (wordEquiv (Finset.equivMap (someEmb V) R)).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  change joinWord b x ((Finset.equivMap (someEmb V) R i).val) = x i.val
  rfl

private theorem conditional_skip {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) (R : Finset V) (z : R → Bool) :
    conditionalMean f (R.map (someEmb V))
        (wordEquiv (Finset.equivMap (someEmb V) R) z) =
      (conditionalMean (fun x => f (joinWord false x)) R z +
        conditionalMean (fun x => f (joinWord true x)) R z) / 2 := by
  classical
  unfold conditionalMean
  rw [← Equiv.piOptionEquivProd.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  have hc : Fintype.card V + 1 - R.card = (Fintype.card V - R.card) + 1 := by
    have := Finset.card_le_univ R
    omega
  simp only [Fintype.card_option, Finset.card_map, hc, pow_succ]
  have hcond : ∀ b x,
      project (R.map (someEmb V)) (Equiv.piOptionEquivProd.symm (b, x)) =
        wordEquiv (Finset.equivMap (someEmb V) R) z ↔ project R x = z := by
    intro b x
    change project (R.map (someEmb V)) (joinWord b x) = _ ↔ _
    rw [project_join]
    exact (wordEquiv _).injective.eq_iff
  simp only [hcond]
  change (_ + _) / ((2 : ℝ≥0) ^ (Fintype.card V - R.card) * 2) = _
  field_simp
  exact add_comm _ _

private theorem conditional_avg {V : Type} [Fintype V] [DecidableEq V]
    (f g : (V → Bool) → ℝ≥0) (R : Finset V) (z : R → Bool) :
    conditionalMean (fun x => (f x + g x) / 2) R z =
      (conditionalMean f R z + conditionalMean g R z) / 2 := by
  classical
  unfold conditionalMean
  have hp : ∀ x : V → Bool,
      (if project R x = z then (f x + g x) / 2 else 0) =
        ((if project R x = z then f x else 0) +
          (if project R x = z then g x else 0)) / 2 := by
    intro x
    split <;> simp
  simp_rw [hp]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  field_simp

private theorem harmonic_skip {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) (R : Finset V) :
    harmonicMean f (R.map (someEmb V)) =
      harmonicMean (fun x => (f (joinWord false x) + f (joinWord true x)) / 2) R := by
  classical
  unfold harmonicMean
  rw [← (wordEquiv (Finset.equivMap (someEmb V) R)).sum_comp]
  simp only [Finset.card_map, conditional_skip, conditional_avg]

private def coordInclude {V : Type} [DecidableEq V] (R : Finset V) :
    ↥(insert none (R.map (someEmb V))) ≃ Option R where
  toFun i := match hi : i.1 with
    | none => none
    | some a => some ⟨a, by have := i.2; simp [hi, someEmb] at this; exact this⟩
  invFun i := match i with
    | none => ⟨none, Finset.mem_insert_self _ _⟩
    | some a => ⟨some a.1, by simp [someEmb, a.2]⟩
  left_inv i := by
    apply Subtype.ext
    rcases i with ⟨i, hi⟩
    cases i <;> rfl
  right_inv i := by
    cases i <;> rfl

private noncomputable def patternPairs {V : Type} [DecidableEq V] (R : Finset V) :
    (↥(insert none (R.map (someEmb V))) → Bool) ≃ (Bool × (R → Bool)) :=
  (wordEquiv (coordInclude R)).trans Equiv.piOptionEquivProd

private theorem project_include {V : Type} [Fintype V] [DecidableEq V]
    (R : Finset V) (b : Bool) (x : V → Bool) :
    patternPairs R (project (insert none (R.map (someEmb V))) (joinWord b x)) =
      (b, project R x) := by
  classical
  apply Prod.ext
  · rfl
  · funext i
    rfl

private theorem conditional_include {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) (R : Finset V) (b : Bool) (z : R → Bool) :
    conditionalMean f (insert none (R.map (someEmb V))) ((patternPairs R).symm (b,z)) =
      conditionalMean (fun x => f (joinWord b x)) R z := by
  classical
  unfold conditionalMean
  rw [← Equiv.piOptionEquivProd.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  have hn : (none : Option V) ∉ R.map (someEmb V) := by simp [someEmb]
  have hc : Fintype.card V + 1 - (R.card + 1) = Fintype.card V - R.card := by omega
  simp only [Fintype.card_option, Finset.card_insert_of_notMem hn, Finset.card_map, hc]
  have hcond : ∀ b' x,
      project (insert none (R.map (someEmb V))) (Equiv.piOptionEquivProd.symm (b', x)) =
          (patternPairs R).symm (b, z) ↔ b' = b ∧ project R x = z := by
    intro b' x
    rw [← (patternPairs R).apply_eq_iff_eq, Equiv.apply_symm_apply]
    change patternPairs R (project _ (joinWord b' x)) = _ ↔ _
    rw [project_include]
    simp only [Prod.mk.injEq]
  simp only [hcond]
  cases b <;> simp <;> rfl

private theorem harmonic_include {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) (R : Finset V) :
    harmonicMean f (insert none (R.map (someEmb V))) =
      ((2 : ℝ≥0∞)⁻¹ *
        ((harmonicMean (fun x => f (joinWord false x)) R)⁻¹ +
          (harmonicMean (fun x => f (joinWord true x)) R)⁻¹))⁻¹ := by
  classical
  unfold harmonicMean
  rw [← (patternPairs R).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  have hn : (none : Option V) ∉ R.map (someEmb V) := by simp [someEmb]
  simp only [Finset.card_insert_of_notMem hn, Finset.card_map, conditional_include,
    inv_inv, pow_succ]
  congr 1
  rw [ENNReal.mul_inv (by simp) (by simp)]
  ring

private theorem harmonic_finite {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) : harmonicMean f R ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top ((corollary_1 V f f f).2.2.1 R)

private theorem enn_harmonic_pair (a b : ℝ≥0) :
    ((2 : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞)⁻¹ + (b : ℝ≥0∞)⁻¹))⁻¹ =
      ((2 * a * b / (a + b) : ℝ≥0) : ℝ≥0∞) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by positivity
  rw [← ENNReal.coe_inv ha, ← ENNReal.coe_inv hb, ← ENNReal.coe_inv_two,
    ← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_inv (by positivity)]
  apply ENNReal.coe_inj.mpr
  field_simp
  exact add_comm _ _

private noncomputable def subsetPairs (V : Type) [DecidableEq V] :
    Finset (Option V) ≃ Bool × Finset V where
  toFun R := (decide (none ∈ R), R.eraseNone)
  invFun p := if p.1 then insert none (p.2.map (someEmb V)) else p.2.map (someEmb V)
  left_inv R := by
    ext i
    by_cases h : none ∈ R <;> cases i <;> simp [someEmb, h]
  right_inv p := by
    rcases p with ⟨b, R⟩
    cases b
    · apply Prod.ext
      · simp [someEmb]
      · ext x
        simp [Finset.mem_eraseNone, someEmb]
    · apply Prod.ext
      · simp [someEmb]
      · ext x
        simp [Finset.mem_eraseNone, someEmb]

private theorem setMean_split {V : Type} [Fintype V] [DecidableEq V]
    (a : Finset (Option V) → ℝ≥0∞) :
    setMean quarterBias a =
      ∑ R : Finset V, ENNReal.ofReal (setWeight quarterBias R) *
        (ENNReal.ofReal (3 / 4) * a (R.map (someEmb V)) +
          ENNReal.ofReal (1 / 4) * a (insert none (R.map (someEmb V)))) := by
  classical
  unfold setMean
  rw [← (subsetPairs V).symm.sum_comp
    (fun R : Finset (Option V) => ENNReal.ofReal (setWeight quarterBias R) * a R),
    Fintype.sum_prod_type, Fintype.sum_bool]
  have hn : ∀ R : Finset V, (none : Option V) ∉ R.map (someEmb V) := by
    intro R
    simp [someEmb]
  have hw0 : ∀ R : Finset V,
      setWeight quarterBias (R.map (someEmb V)) = (3 / 4 : ℝ) * setWeight quarterBias R := by
    intro R
    have hc : Fintype.card V + 1 - R.card = (Fintype.card V - R.card) + 1 := by
      have := Finset.card_le_univ R
      omega
    simp only [setWeight, quarterBias, Fintype.card_option, Finset.card_map, hc, pow_succ]
    ring
  have hw1 : ∀ R : Finset V,
      setWeight quarterBias (insert none (R.map (someEmb V))) =
        (1 / 4 : ℝ) * setWeight quarterBias R := by
    intro R
    simp only [setWeight, quarterBias, Fintype.card_option,
      Finset.card_insert_of_notMem (hn R), Finset.card_map]
    rw [show Fintype.card V + 1 - (R.card + 1) = Fintype.card V - R.card by omega,
      pow_succ]
    ring
  have ht : ∀ R : Finset V, (subsetPairs V).symm (true, R) =
      insert none (R.map (someEmb V)) := fun R => rfl
  have hf : ∀ R : Finset V, (subsetPairs V).symm (false, R) =
      R.map (someEmb V) := fun R => rfl
  simp_rw [ht, hf]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  rw [hw0, hw1, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
  ring

private theorem cubeMean_join {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) :
    cubeMean f =
      (cubeMean (fun x => f (joinWord false x)) +
        cubeMean (fun x => f (joinWord true x))) / 2 := by
  classical
  unfold cubeMean
  rw [← Equiv.piOptionEquivProd.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_option, pow_succ, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  exact add_comm _ _

private theorem two_point_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) / 2 ≤
      (3 / 4 : ℝ) * Real.sqrt ((a + b) / 2) +
        (1 / 4 : ℝ) * Real.sqrt (2 * a * b / (a + b)) := by
  by_cases hab : a + b = 0
  · have haa : a = 0 := by linarith
    have hbb : b = 0 := by linarith
    simp [haa, hbb]
  · have habpos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    let u := Real.sqrt a
    let v := Real.sqrt b
    let c := Real.sqrt ((a + b) / 2)
    let e := Real.sqrt (2 * a * b / (a + b))
    have hu : 0 ≤ u := Real.sqrt_nonneg _
    have hv : 0 ≤ v := Real.sqrt_nonneg _
    have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
    have he : 0 ≤ e := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = a := Real.sq_sqrt ha
    have hv2 : v ^ 2 = b := Real.sq_sqrt hb
    have hc2 : c ^ 2 = (a + b) / 2 := Real.sq_sqrt (by positivity)
    have he2 : e ^ 2 = 2 * a * b / (a + b) := Real.sq_sqrt (by positivity)
    have hec2 : (e * c) ^ 2 = (u * v) ^ 2 := by
      rw [mul_pow, he2, hc2, mul_pow, hu2, hv2]
      field_simp
    have hec : e * c = u * v :=
      (sq_eq_sq₀ (mul_nonneg he hc.le) (mul_nonneg hu hv)).mp hec2
    change (u + v) / 2 ≤ 3 / 4 * c + 1 / 4 * e
    nlinarith [sq_nonneg (2 * c - u - v)]

private theorem two_point_enn (a b c : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (hc : c ≠ ∞) (havg : (2 : ℝ≥0∞)⁻¹ * (a + b) ≤ c) :
    (2 : ℝ≥0∞)⁻¹ * (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (3 / 4) * c ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (1 / 4) *
          ((2 : ℝ≥0∞)⁻¹ * (a⁻¹ + b⁻¹))⁻¹ ^ (1 / 2 : ℝ) := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  lift c to ℝ≥0 using hc
  rw [enn_harmonic_pair]
  have havgNN : (a + b) / 2 ≤ c := by
    apply ENNReal.coe_le_coe.mp
    simpa [ENNReal.coe_div, ENNReal.coe_add, div_eq_mul_inv, mul_comm] using havg
  have habreal := two_point_sqrt (a : ℝ) (b : ℝ) a.coe_nonneg b.coe_nonneg
  have hcmono : Real.sqrt (((a : ℝ) + b) / 2) ≤ Real.sqrt (c : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast havgNN)
  have hreal : (Real.sqrt (a : ℝ) + Real.sqrt (b : ℝ)) / 2 ≤
      (3 / 4 : ℝ) * Real.sqrt (c : ℝ) +
        (1 / 4 : ℝ) * Real.sqrt (2 * (a : ℝ) * b / (a + b)) := by
    linarith
  have hNN :
      (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) / 2 ≤
        (3 / 4 : ℝ≥0) * c ^ (1 / 2 : ℝ) +
          (1 / 4 : ℝ≥0) * (2 * a * b / (a + b)) ^ (1 / 2 : ℝ) := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_rpow,
      NNReal.coe_ofNat, NNReal.coe_one, Real.sqrt_eq_rpow] using hreal
  have h34 : ENNReal.ofReal (3 / 4) = ((3 / 4 : ℝ≥0) : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h14 : ENNReal.ofReal (1 / 4) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [h34, h14, ← ENNReal.coe_inv_two,
    ← ENNReal.coe_rpow_of_nonneg a (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.coe_rpow_of_nonneg b (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.coe_rpow_of_nonneg c (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.coe_rpow_of_nonneg (2*a*b/(a+b)) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_cast
  simpa [div_eq_mul_inv, mul_comm] using hNN

private theorem step_pointwise {V : Type} [Fintype V] [DecidableEq V]
    (f : (Option V → Bool) → ℝ≥0) (R : Finset V) :
    (2 : ℝ≥0∞)⁻¹ *
        ((harmonicMean (fun x => f (joinWord false x)) R) ^ (1 / 2 : ℝ) +
          (harmonicMean (fun x => f (joinWord true x)) R) ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (3 / 4) * (harmonicMean f (R.map (someEmb V))) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (1 / 4) *
          (harmonicMean f (insert none (R.map (someEmb V)))) ^ (1 / 2 : ℝ) := by
  let f0 : (V → Bool) → ℝ≥0 := fun x => f (joinWord false x)
  let f1 : (V → Bool) → ℝ≥0 := fun x => f (joinWord true x)
  let favg : (V → Bool) → ℝ≥0 := fun x => (f0 x + f1 x) / 2
  have hh : (1 - (1 / 2 : ℝ≥0)) = 1 / 2 := by
    apply NNReal.coe_inj.mp
    rw [NNReal.coe_sub (by norm_num)]
    norm_num
  have hlin : ∀ x, favg x = (1 / 2 : ℝ≥0) * f0 x + (1 - (1 / 2 : ℝ≥0)) * f1 x := by
    intro x
    dsimp [favg]
    rw [hh]
    ring
  have hconc := (corollary_1 V favg f0 f1).1 (1/2) (by norm_num) hlin R
  have hc : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by norm_num
  rw [hh, hc, ← mul_add] at hconc
  rw [harmonic_skip, harmonic_include]
  exact two_point_enn _ _ _ (harmonic_finite f0 R) (harmonic_finite f1 R)
    (harmonic_finite favg R) hconc

private theorem cubeMean_relabel {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (f : (V → Bool) → ℝ≥0) :
    cubeMean (fun y => f ((wordEquiv e).symm y)) = cubeMean f := by
  classical
  unfold cubeMean
  rw [← (wordEquiv e).sum_comp]
  simp only [Equiv.symm_apply_apply, ← Fintype.card_congr (wordEquiv e)]

private theorem setMean_relabel {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (f : (V → Bool) → ℝ≥0) :
    setMean quarterBias (fun R =>
      (harmonicMean (fun y => f ((wordEquiv e).symm y)) R) ^ (1 / 2 : ℝ)) =
    setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by
  classical
  unfold setMean
  rw [← e.finsetCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro R hR
  simp only [Equiv.finsetCongr_apply, harmonic_relabel]
  congr 2
  simp only [setWeight, Finset.card_map, ← Fintype.card_congr e]

private theorem tensor_empty [DecidableEq PEmpty.{1}] (f : (PEmpty → Bool) → ℝ≥0) :
    (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
      setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by
  classical
  have hH : harmonicMean f ∅ = (cubeMean f : ℝ≥0∞) :=
    (corollary_1 PEmpty f f f).2.2.2.symm
  have hR : ∀ R : Finset PEmpty.{1}, R = ∅ := fun R => Subsingleton.elim _ _
  simp only [setMean]
  simp_rw [hR]
  simp only [setWeight, quarterBias, Finset.card_empty, Fintype.card_eq_zero,
    Nat.sub_zero, pow_zero, mul_one, ENNReal.ofReal_one, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_finset, pow_zero, one_smul]
  rw [hH]
  simp only [cubeMean, Fintype.card_fun, Fintype.card_eq_zero, pow_zero,
    Nat.cast_one, div_one]
  simp
  exact le_of_eq (ENNReal.coe_rpow_of_nonneg _ (by positivity))

private theorem tensor_option {V : Type} [Fintype V] [DecidableEq V]
    (ih : ∀ f : (V → Bool) → ℝ≥0,
      (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
        setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)))
    (f : (Option V → Bool) → ℝ≥0) :
    (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
      setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by
  classical
  let f0 : (V → Bool) → ℝ≥0 := fun x => f (joinWord false x)
  let f1 : (V → Bool) → ℝ≥0 := fun x => f (joinWord true x)
  let a : Finset V → ℝ≥0∞ := fun R => (harmonicMean f0 R) ^ (1 / 2 : ℝ)
  let b : Finset V → ℝ≥0∞ := fun R => (harmonicMean f1 R) ^ (1 / 2 : ℝ)
  have hsum : (2 : ℝ≥0∞)⁻¹ * (setMean quarterBias a + setMean quarterBias b) =
      ∑ R : Finset V, ENNReal.ofReal (setWeight quarterBias R) * (2⁻¹ * (a R + b R)) := by
    simp only [setMean, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro R hR <;> ring
  rw [cubeMean_join (fun x => f x ^ (1 / 2 : ℝ))]
  rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_add]
  simp only [ENNReal.coe_ofNat]
  rw [div_eq_mul_inv, mul_comm]
  calc
    (2 : ℝ≥0∞)⁻¹ *
        ((cubeMean (fun x => f0 x ^ (1 / 2 : ℝ)) : ℝ≥0∞) +
          (cubeMean (fun x => f1 x ^ (1 / 2 : ℝ)) : ℝ≥0∞))
        ≤ 2⁻¹ * (setMean quarterBias a + setMean quarterBias b) := by
      simpa only [mul_comm] using
        mul_le_mul_left (add_le_add (ih f0) (ih f1)) ((2 : ℝ≥0∞)⁻¹)
    _ = ∑ R : Finset V, ENNReal.ofReal (setWeight quarterBias R) *
          (2⁻¹ * (a R + b R)) := hsum
    _ ≤ ∑ R : Finset V, ENNReal.ofReal (setWeight quarterBias R) *
        (ENNReal.ofReal (3 / 4) * (harmonicMean f (R.map (someEmb V))) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (1 / 4) *
            (harmonicMean f (insert none (R.map (someEmb V)))) ^ (1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro R hR
      simpa only [mul_comm] using mul_le_mul_left (step_pointwise f R)
        (ENNReal.ofReal (setWeight quarterBias R))
    _ = setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) :=
      (setMean_split (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ))).symm

private theorem tensor_all (V : Type) [Fintype V] :
    ∀ [DecidableEq V] (f : (V → Bool) → ℝ≥0),
      (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
        setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun T _ => ∀ [DecidableEq T] (f : (T → Bool) → ℝ≥0),
      (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
        setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ))) ?_ ?_ ?_ V
  · intro A B instB e ih instEqB f
    letI : Fintype A := Fintype.ofEquiv B e.symm
    letI : DecidableEq A := Classical.decEq A
    let g : (A → Bool) → ℝ≥0 := fun x => f (wordEquiv e x)
    have hg := ih g
    have hm := cubeMean_relabel e (fun x => g x ^ (1 / 2 : ℝ))
    have hs := setMean_relabel e g
    simp only [g, Equiv.apply_symm_apply] at hm hs
    rw [hm, hs]
    exact hg
  · intro instEq f
    exact tensor_empty f
  · intro A instA ih instEqOption f
    letI : DecidableEq A := Classical.decEq A
    have heq : instEqOption = @Option.instDecidableEq A (Classical.decEq A) :=
      Subsingleton.elim _ _
    cases heq
    exact tensor_option (fun g => ih g) f

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) :
    (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
      setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by
  exact tensor_all V f
