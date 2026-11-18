-- Prove2me | solution 1 for TopDownParity1043.Main.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:52:45.449572+00:00
-- url     : https://prove2.me/submissions/0aa0fca0-9ee4-4dfe-8300-c01d27291da6

import Mathlib
import Definitions.Def_TopDownParity1043_Main_HarmonicMean
import Theorems.Thm_TopDownParity1043_Main_lemma_11

set_option autoImplicit false
open scoped NNReal ENNReal
open TopDownParity1043.Main

private def completionEquiv (V : Type) [Fintype V] [DecidableEq V]
    (T : Finset V) (z : T → Bool) :
    {x : V → Bool // project T x = z} ≃ ({v : V // v ∉ T} → Bool) where
  toFun x v := x.1 v.1
  invFun y := ⟨fun v => if hv : v ∈ T then z ⟨v, hv⟩ else y ⟨v, hv⟩, by
    funext i
    simp [project, i.property]⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ T
    · have h := congrFun x.2 ⟨v, hv⟩
      dsimp
      rw [dif_pos hv]
      simpa only [project] using h.symm
    · simp [hv]
  right_inv y := by
    funext v
    simp [v.2]

private theorem completion_count (V : Type) [Fintype V] [DecidableEq V]
    (T : Finset V) (z : T → Bool) :
    (Finset.univ.filter fun x : V → Bool => project T x = z).card =
      2 ^ (Fintype.card V - T.card) := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (completionEquiv V T z)]
  simp

private theorem uniform_weight_sum (V : Type) [Fintype V] [DecidableEq V] (T : Finset V) :
    ∑ _ : T → Bool, ((2 : ℝ≥0) ^ T.card)⁻¹ = 1 := by
  simp [Fintype.card_congr (Equiv.Set.univ _)]

private theorem conditionalMean_one (V : Type) [Fintype V] [DecidableEq V] (T : Finset V)
    (z : T → Bool) :
    conditionalMean (fun _ : V → Bool => (1 : ℝ≥0)) T z = 1 := by
  classical
  simp [conditionalMean]
  rw [completion_count]
  simp

private theorem uniform_energy_eq (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (T : Finset V) (u : (T → Bool) → ℝ≥0) :
    weightedEnergy (fun _ : T → Bool => ((2 : ℝ≥0) ^ T.card)⁻¹)
        (conditionalMean f T) u =
      (∑ x, f x * u (project T x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V := by
  classical
  let a : ℝ≥0 := (2 : ℝ≥0) ^ T.card
  let b : ℝ≥0 := (2 : ℝ≥0) ^ (Fintype.card V - T.card)
  have ha : a ≠ 0 := pow_ne_zero _ two_ne_zero
  have hb : b ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcard : T.card ≤ Fintype.card V := Finset.card_le_univ T
  have hab : a * b = (2 : ℝ≥0) ^ Fintype.card V := by
    simp only [a, b, ← pow_add]
    rw [Nat.add_sub_of_le hcard]
  simp only [weightedEnergy, conditionalMean]
  rw [show ∑ z : T → Bool,
      a⁻¹ * ((∑ x : V → Bool, if project T x = z then f x else 0) / b) * u z ^ 2 =
      (∑ z : T → Bool, ∑ x : V → Bool,
        if project T x = z then f x * u z ^ 2 else 0) / (a * b) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    field_simp [ha, hb]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    split <;> rename_i h
    · exact mul_comm _ _
    · exact zero_mul _]
  rw [hab]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

private theorem harmonic_eq_weighted (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) :
    harmonicMean f R =
      weightedHarmonic (fun _ : R → Bool => ((2 : ℝ≥0) ^ R.card)⁻¹)
        (conditionalMean f R) := by
  classical
  simp only [harmonicMean, weightedHarmonic,
    ENNReal.coe_inv (pow_ne_zero _ two_ne_zero)]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp

private theorem uniform_pullback_mean (V : Type) [Fintype V] [DecidableEq V]
    (R S : Finset V) (hRS : R ⊆ S) (w : (R → Bool) → ℝ≥0) :
    ∑ z : S → Bool, ((2 : ℝ≥0) ^ S.card)⁻¹ *
        w (fun i => z ⟨i.1, hRS i.2⟩) =
      ∑ z : R → Bool, ((2 : ℝ≥0) ^ R.card)⁻¹ * w z := by
  classical
  let res : (S → Bool) → (R → Bool) := fun z i => z ⟨i.1, hRS i.2⟩
  let uS : (S → Bool) → ℝ≥0 := fun z => NNReal.sqrt (w (res z))
  let uR : (R → Bool) → ℝ≥0 := fun z => NNReal.sqrt (w z)
  have hproj : ∀ x : V → Bool, res (project S x) = project R x := by
    intro x
    funext i
    rfl
  have henergy :
      weightedEnergy (fun _ : S → Bool => ((2 : ℝ≥0) ^ S.card)⁻¹)
          (conditionalMean (fun _ : V → Bool => (1 : ℝ≥0)) S) uS =
        weightedEnergy (fun _ : R → Bool => ((2 : ℝ≥0) ^ R.card)⁻¹)
          (conditionalMean (fun _ : V → Bool => (1 : ℝ≥0)) R) uR := by
    rw [uniform_energy_eq, uniform_energy_eq]
    congr 1
  simpa [weightedEnergy, conditionalMean_one, uS, uR, res] using henergy

private theorem harmonic_antitone (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R S : Finset V) (hRS : R ⊆ S) :
    harmonicMean f S ≤ harmonicMean f R := by
  classical
  let pR : (R → Bool) → ℝ≥0 := fun _ => ((2 : ℝ≥0) ^ R.card)⁻¹
  let pS : (S → Bool) → ℝ≥0 := fun _ => ((2 : ℝ≥0) ^ S.card)⁻¹
  have hpR : ∀ z, 0 < pR z := by
    intro z
    simp [pR]
  have hpS : ∀ z, 0 < pS z := by
    intro z
    simp [pS]
  have hpR1 : ∑ z, pR z = 1 := by simpa [pR] using uniform_weight_sum V R
  have hpS1 : ∑ z, pS z = 1 := by simpa [pS] using uniform_weight_sum V S
  rw [harmonic_eq_weighted V f S, harmonic_eq_weighted V f R,
    lemma_11 _ pS (conditionalMean f S) hpS hpS1,
    lemma_11 _ pR (conditionalMean f R) hpR hpR1]
  apply le_iInf
  intro wR
  apply le_iInf
  intro hwR
  let wS : (S → Bool) → ℝ≥0 := fun z => wR (fun i => z ⟨i.1, hRS i.2⟩)
  have hwS : ∑ z, pS z * wS z = 1 := by
    rw [show ∑ z, pS z * wS z = ∑ z, pR z * wR z by
      simpa [pS, pR, wS] using uniform_pullback_mean V R S hRS wR]
    exact hwR
  calc
    ⨅ (w : (S → Bool) → ℝ≥0) (_ : ∑ z, pS z * w z = 1),
        (weightedEnergy pS (conditionalMean f S) w : ℝ≥0∞)
        ≤ ⨅ (_ : ∑ z, pS z * wS z = 1),
            (weightedEnergy pS (conditionalMean f S) wS : ℝ≥0∞) := iInf_le _ wS
    _ ≤ (weightedEnergy pS (conditionalMean f S) wS : ℝ≥0∞) := iInf_le _ hwS
    _ = (weightedEnergy pR (conditionalMean f R) wR : ℝ≥0∞) := by
      apply ENNReal.coe_inj.mpr
      rw [show weightedEnergy pS (conditionalMean f S) wS =
          (∑ x, f x * wS (project S x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V by
        simpa [pS] using uniform_energy_eq V f S wS]
      rw [show weightedEnergy pR (conditionalMean f R) wR =
          (∑ x, f x * wR (project R x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V by
        simpa [pR] using uniform_energy_eq V f R wR]
      congr 2

private theorem harmonic_concave (V : Type) [Fintype V] [DecidableEq V]
    (f g h : (V → Bool) → ℝ≥0) (lam : ℝ≥0) (hlam : lam ≤ 1)
    (hfg : ∀ x, f x = lam * g x + (1 - lam) * h x) (R : Finset V) :
    (lam : ℝ≥0∞) * harmonicMean g R +
      ((1 - lam : ℝ≥0) : ℝ≥0∞) * harmonicMean h R ≤ harmonicMean f R := by
  classical
  let p : (R → Bool) → ℝ≥0 := fun _ => ((2 : ℝ≥0) ^ R.card)⁻¹
  have hp : ∀ z, 0 < p z := by
    intro z
    simp [p]
  have hp1 : ∑ z, p z = 1 := by simpa [p] using uniform_weight_sum V R
  rw [harmonic_eq_weighted V f R, harmonic_eq_weighted V g R,
    harmonic_eq_weighted V h R,
    lemma_11 _ p (conditionalMean f R) hp hp1,
    lemma_11 _ p (conditionalMean g R) hp hp1,
    lemma_11 _ p (conditionalMean h R) hp hp1]
  apply le_iInf
  intro w
  apply le_iInf
  intro hw
  have hg_le :
      (⨅ (v : (R → Bool) → ℝ≥0) (_ : ∑ z, p z * v z = 1),
        (weightedEnergy p (conditionalMean g R) v : ℝ≥0∞)) ≤
        (weightedEnergy p (conditionalMean g R) w : ℝ≥0∞) :=
    le_trans (iInf_le _ w) (iInf_le _ hw)
  have hh_le :
      (⨅ (v : (R → Bool) → ℝ≥0) (_ : ∑ z, p z * v z = 1),
        (weightedEnergy p (conditionalMean h R) v : ℝ≥0∞)) ≤
        (weightedEnergy p (conditionalMean h R) w : ℝ≥0∞) :=
    le_trans (iInf_le _ w) (iInf_le _ hw)
  have hlin :
      weightedEnergy p (conditionalMean f R) w =
        lam * weightedEnergy p (conditionalMean g R) w +
          (1 - lam) * weightedEnergy p (conditionalMean h R) w := by
    rw [show weightedEnergy p (conditionalMean f R) w =
        (∑ x, f x * w (project R x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V by
      simpa [p] using uniform_energy_eq V f R w]
    rw [show weightedEnergy p (conditionalMean g R) w =
        (∑ x, g x * w (project R x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V by
      simpa [p] using uniform_energy_eq V g R w]
    rw [show weightedEnergy p (conditionalMean h R) w =
        (∑ x, h x * w (project R x) ^ 2) / (2 : ℝ≥0) ^ Fintype.card V by
      simpa [p] using uniform_energy_eq V h R w]
    field_simp [pow_ne_zero _ two_ne_zero]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    congr 1
    funext x
    rw [hfg x]
    ring
  calc
    (lam : ℝ≥0∞) *
          (⨅ (v : (R → Bool) → ℝ≥0) (_ : ∑ z, p z * v z = 1),
            (weightedEnergy p (conditionalMean g R) v : ℝ≥0∞)) +
        ((1 - lam : ℝ≥0) : ℝ≥0∞) *
          (⨅ (v : (R → Bool) → ℝ≥0) (_ : ∑ z, p z * v z = 1),
            (weightedEnergy p (conditionalMean h R) v : ℝ≥0∞))
        ≤ (lam : ℝ≥0∞) * (weightedEnergy p (conditionalMean g R) w : ℝ≥0∞) +
          ((1 - lam : ℝ≥0) : ℝ≥0∞) *
            (weightedEnergy p (conditionalMean h R) w : ℝ≥0∞) :=
      add_le_add
        (by simpa [mul_comm] using mul_le_mul_left hg_le (lam : ℝ≥0∞))
        (by simpa [mul_comm] using
          mul_le_mul_left hh_le ((1 - lam : ℝ≥0) : ℝ≥0∞))
    _ = (weightedEnergy p (conditionalMean f R) w : ℝ≥0∞) := by
      rw [hlin]
      simp

private theorem cubeMean_eq_harmonic_empty (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) :
    (cubeMean f : ℝ≥0∞) = harmonicMean f ∅ := by
  classical
  have hproj : ∀ x : V → Bool, project ∅ x = default :=
    fun x => Subsingleton.elim _ _
  have hempty : (fun _ : (∅ : Finset V) => false) = default :=
    Subsingleton.elim _ _
  simp [cubeMean, harmonicMean, conditionalMean, hproj]
  split
  · simp
  · rename_i h
    exact (h (Subsingleton.elim _ _)).elim

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (f g h : (V → Bool) → ℝ≥0) :
    (∀ lam : ℝ≥0, lam ≤ 1 → (∀ x, f x = lam * g x + (1 - lam) * h x) →
      ∀ R : Finset V, (lam : ℝ≥0∞) * harmonicMean g R +
        ((1 - lam : ℝ≥0) : ℝ≥0∞) * harmonicMean h R ≤ harmonicMean f R) ∧
    (∀ R S : Finset V, R ⊆ S → harmonicMean f S ≤ harmonicMean f R) ∧
    (∀ R : Finset V, harmonicMean f R ≤ (cubeMean f : ℝ≥0∞)) ∧
    (cubeMean f : ℝ≥0∞) = harmonicMean f ∅ := by
  refine ⟨?_, ?_, ?_, cubeMean_eq_harmonic_empty V f⟩
  · intro lam hlam hfg R
    exact harmonic_concave V f g h lam hlam hfg R
  · intro R S hRS
    exact harmonic_antitone V f R S hRS
  · intro R
    have hmono := harmonic_antitone V f ∅ R (Finset.empty_subset R)
    rw [← cubeMean_eq_harmonic_empty V f] at hmono
    exact hmono
