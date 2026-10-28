-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P27.label_mean_shannon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:48:31.068069+00:00
-- url     : https://prove2.me/submissions/bc74137a-12d9-4ee3-9205-bdd52aa9ed69

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27
noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)
open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)
open QAlgorithms.Papers.Independent.Support50.P27
attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)
open Real (negMulLog)

theorem S196L_sh {Y : Type} [Fintype Y] (q : Y → ℝ) :
    shannon q * Real.log 2 = ∑ i, negMulLog (q i) := by
  have h2 : Real.log 2 ≠ 0 := by positivity
  unfold shannon Real.logb negMulLog
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem S196L_chain {X Y : Type} [Fintype X] [Fintype Y] (w : X → ℝ) (F : X → Y → ℝ)
    (hF : ∀ x, ∑ y, F x y = 1) :
    (shannon w + shannon (fun y => ∑ x, w x * F x y) -
        shannon (fun z : X × Y => w z.1 * F z.1 z.2)) * Real.log 2 =
      ∑ y, negMulLog (∑ x, w x * F x y) - ∑ x, w x * ∑ y, negMulLog (F x y) := by
  rw [sub_mul, add_mul, S196L_sh, S196L_sh, S196L_sh, Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, hF, one_mul,
    Finset.mul_sum]
  ring

theorem S196L_subadd {X : Type} [Fintype X] (j : X → ℝ) (hj : ∀ i, 0 ≤ j i) :
    negMulLog (∑ i, j i) ≤ ∑ i, negMulLog (j i) := by
  unfold negMulLog
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases (hj i).lt_or_eq with h | h
  · have : Real.log (j i) ≤ Real.log (∑ i, j i) :=
      Real.log_le_log h (Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ i))
    nlinarith
  · rw [← h]; simp

theorem S196L_jensen {X : Type} [Fintype X] (w z : X → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, 0 ≤ z i) : ∃ c, 0 ≤ c ∧ ∑ i, w i * z i = (∑ i, w i) * c ∧
      ∑ i, w i * negMulLog (z i) ≤ (∑ i, w i) * negMulLog c := by
  by_cases hW : ∑ i, w i = 0
  · have h0 : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw k)).mp hW i (Finset.mem_univ i)
    exact ⟨0, le_refl _, by simp [h0], by simp [h0]⟩
  · have hWp : 0 < ∑ i, w i := lt_of_le_of_ne (Finset.sum_nonneg fun k _ => hw k) (Ne.symm hW)
    refine ⟨(∑ i, w i * z i) / ∑ i, w i, div_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hw k) (hz k)) hWp.le, by field_simp, ?_⟩
    have J := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun i => w i / ∑ k, w k) (p := z) (fun i _ => div_nonneg (hw i) hWp.le)
      (by rw [← Finset.sum_div]; field_simp) (fun i _ => Set.mem_Ici.mpr (hz i))
    simp only [smul_eq_mul, div_mul_eq_mul_div, ← Finset.sum_div] at J
    rw [div_le_iff₀ hWp, mul_comm] at J
    exact J

theorem S196L_scalar (a c p : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (negMulLog (1/2 * (p*a + (1-p)*c) + 1/2 * a) -
        (1/2 * negMulLog (p*a + (1-p)*c) + 1/2 * negMulLog a)) ≤
      negMulLog (p*a + (1-p)*c) - p * negMulLog a - (1-p) * negMulLog c := by
  have hcv := Real.concaveOn_negMulLog
  have h1 : p * negMulLog a + (1-p) * negMulLog c ≤ negMulLog (p*a + (1-p)*c) := by
    have := hcv.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hc) hp0
      (show (0:ℝ) ≤ 1 - p by linarith) (by ring)
    simpa [smul_eq_mul] using this
  set s := (1 + p) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hu : 0 ≤ s * a + (1 - s) * c := by
    have : 0 ≤ 1 - s := by rw [hs]; linarith
    positivity
  have hmu0 : 0 ≤ p / s := div_nonneg hp0 hs0.le
  have hmu1 : 0 ≤ 1 - p / s := by
    rw [sub_nonneg, div_le_one hs0, hs]; linarith
  have h2 := hcv.2 (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hc) hmu0 hmu1 (by ring)
  simp only [smul_eq_mul] at h2
  have e1 : p / s * (s * a + (1 - s) * c) + (1 - p / s) * c = p*a + (1-p)*c := by
    field_simp; rw [hs]; ring
  have e2 : 1/2 * (p*a + (1-p)*c) + 1/2 * a = s * a + (1 - s) * c := by rw [hs]; ring
  rw [e1] at h2
  rw [e2]
  have h3 : p * negMulLog (s * a + (1 - s) * c) + (s - p) * negMulLog c ≤
      s * negMulLog (p*a + (1-p)*c) := by
    have := mul_le_mul_of_nonneg_left h2 hs0.le
    have e3 : s * (p / s * negMulLog (s * a + (1 - s) * c) + (1 - p / s) * negMulLog c) =
        p * negMulLog (s * a + (1 - s) * c) + (s - p) * negMulLog c := by
      field_simp
    linarith
  rw [hs] at h3
  nlinarith

theorem S196L_core {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] (p : X → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (P : X → Y → ℝ) (hP0 : ∀ x y, 0 ≤ P x y)
    (x : X) :
    p x * (∑ y, negMulLog (1/2 * (∑ x', p x' * P x' y) + 1/2 * P x y) -
        (1/2 * ∑ y, negMulLog (∑ x', p x' * P x' y) + 1/2 * ∑ y, negMulLog (P x y))) ≤
      ∑ y, negMulLog (∑ x', p x' * P x' y) - ∑ x', p x' * ∑ y, negMulLog (P x' y) := by
  set w : X → ℝ := fun x' => if x' = x then 0 else p x' with hw
  have hw0 : ∀ x', 0 ≤ w x' := fun x' => by simp only [hw]; split_ifs <;> simp [hp0]
  have hsplit : ∀ f : X → ℝ, ∑ x', p x' * f x' = p x * f x + ∑ x', w x' * f x' := by
    intro f
    have : ∀ x', w x' * f x' = p x' * f x' - if x' = x then p x * f x else 0 := by
      intro x'; by_cases h : x' = x <;> simp [hw, h]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hW : ∑ x', w x' = 1 - p x := by
    have := hsplit (fun _ => 1); simp only [mul_one] at this; linarith
  have hpx1 : p x ≤ 1 := by
    rw [← hp1]; exact Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ x)
  have hy : ∀ y, p x * (negMulLog (1/2 * (∑ x', p x' * P x' y) + 1/2 * P x y) -
        (1/2 * negMulLog (∑ x', p x' * P x' y) + 1/2 * negMulLog (P x y))) ≤
      negMulLog (∑ x', p x' * P x' y) - ∑ x', p x' * negMulLog (P x' y) := by
    intro y
    obtain ⟨c, hc0, hc1, hc2⟩ := S196L_jensen w (fun x' => P x' y) hw0 (fun x' => hP0 x' y)
    rw [hW] at hc1 hc2
    have hb : ∑ x', p x' * P x' y = p x * P x y + (1 - p x) * c := by
      rw [hsplit (fun x' => P x' y), hc1]
    rw [hsplit (fun x' => negMulLog (P x' y)), hb]
    have := S196L_scalar (P x y) c (p x) (hP0 x y) hc0 (hp0 x) hpx1
    linarith
  have := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hy y
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
  have e : ∑ x', p x' * ∑ y, negMulLog (P x' y) = ∑ y, ∑ x', p x' * negMulLog (P x' y) := by
    rw [Finset.sum_comm]; simp [Finset.mul_sum]
  rw [e]; linarith

/-! Quantum layer. -/

variable {E : Type} [Fintype E] [DecidableEq E]

def S196L_val {X : Type} [Fintype X] (p : X → ℝ) (M : Measurement E)
    (ρ : X → Matrix E E ℂ) : ℝ :=
  shannon p + shannon (fun y => ∑ x, p x * QAlgorithms.effectProb (M.effect y) (ρ x)) -
    shannon (fun z : X × Fin M.outcomes => p z.1 * QAlgorithms.effectProb (M.effect z.2) (ρ z.1))

omit [DecidableEq E] in
open scoped MatrixOrder in
theorem S196L_eff_nonneg {K R : Matrix E E ℂ}
    (hK : K.PosSemidef) (hR : R.PosSemidef) : 0 ≤ QAlgorithms.effectProb K R := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
  unfold QAlgorithms.effectProb
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h := (hR.mul_mul_conjTranspose_same B).trace_nonneg
  rw [Matrix.star_eq_conjTranspose]
  have := Complex.nonneg_iff.mp h
  linarith [this.1]

theorem S196L_eff_sum (M : Measurement E) (R : Matrix E E ℂ) :
    ∑ y, QAlgorithms.effectProb (M.effect y) R = R.trace.re := by
  unfold QAlgorithms.effectProb
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, M.valid.2, Matrix.one_mul]

omit [DecidableEq E] in
theorem S196L_eff_mean {X : Type} [Fintype X] (A : CQData X E) (K : Matrix E E ℂ) :
    QAlgorithms.effectProb K (ensembleMean A) =
      ∑ x', A.prob x' * QAlgorithms.effectProb K (A.state x') := by
  unfold ensembleMean QAlgorithms.Papers.Independent.Information100.P27.average
    QAlgorithms.effectProb
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem S196L_upper {X : Type} [Fintype X] (A : CQData X E) (hA : A.Valid)
    (M : Measurement E) : S196L_val A.prob M A.state ≤ shannon A.prob := by
  have hl : 0 < Real.log 2 := by positivity
  have hj : ∀ x y, 0 ≤ A.prob x * QAlgorithms.effectProb (M.effect y) (A.state x) :=
    fun x y => mul_nonneg (hA.1 x) (S196L_eff_nonneg (M.valid.1 y) (hA.2.2 x).1)
  have key : shannon (fun y => ∑ x, A.prob x * QAlgorithms.effectProb (M.effect y) (A.state x))
      * Real.log 2 ≤ shannon (fun z : X × Fin M.outcomes =>
        A.prob z.1 * QAlgorithms.effectProb (M.effect z.2) (A.state z.1)) * Real.log 2 := by
    rw [S196L_sh, S196L_sh, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_le_sum fun y _ => S196L_subadd _ fun x => hj x y
  have := le_of_mul_le_mul_right key hl
  unfold S196L_val
  linarith

theorem S196L_pointwise {X : Type} [Fintype X] (A : CQData X E) (hA : A.Valid)
    (M : Measurement E) (x : X) :
    A.prob x * S196L_val (fun _ : Bool => (1/2 : ℝ)) M
        (fun b => if b then ensembleMean A else A.state x) ≤
      S196L_val A.prob M A.state := by
  have hl : 0 < Real.log 2 := by positivity
  set P : X → Fin M.outcomes → ℝ := fun x' y => QAlgorithms.effectProb (M.effect y) (A.state x')
    with hP
  have hP1 : ∀ x', ∑ y, P x' y = 1 := by
    intro x'; simp only [hP]; rw [S196L_eff_sum, (hA.2.2 x').2]; simp
  have hP0 : ∀ x' y, 0 ≤ P x' y := fun x' y => S196L_eff_nonneg (M.valid.1 y) (hA.2.2 x').1
  set F : Bool → Fin M.outcomes → ℝ := fun b y =>
    QAlgorithms.effectProb (M.effect y) (if b then ensembleMean A else A.state x) with hF
  have hFt : ∀ y, F true y = ∑ x', A.prob x' * P x' y := by
    intro y; simp only [hF, hP, if_true]; exact S196L_eff_mean A _
  have hFf : ∀ y, F false y = P x y := by intro y; simp [hF, hP]
  have hF1 : ∀ b, ∑ y, F b y = 1 := by
    intro b; cases b
    · simp only [hFf]; exact hP1 x
    · simp only [hFt]; rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hP1, mul_one]; exact hA.2.1
  have cA : S196L_val A.prob M A.state * Real.log 2 = _ := S196L_chain A.prob P hP1
  have cB : S196L_val (fun _ : Bool => (1/2 : ℝ)) M
        (fun b => if b then ensembleMean A else A.state x) * Real.log 2 =
      ∑ y, negMulLog (1/2 * (∑ x', A.prob x' * P x' y) + 1/2 * P x y) -
        (1/2 * ∑ y, negMulLog (∑ x', A.prob x' * P x' y) + 1/2 * ∑ y, negMulLog (P x y)) := by
    rw [show S196L_val (fun _ : Bool => (1/2 : ℝ)) M
        (fun b => if b then ensembleMean A else A.state x) =
        shannon (fun _ : Bool => (1/2 : ℝ)) + shannon (fun y => ∑ b, 1/2 * F b y) -
          shannon (fun z : Bool × Fin M.outcomes => 1/2 * F z.1 z.2) from rfl,
      S196L_chain _ F hF1]
    simp only [Fintype.sum_bool, hFt, hFf]
  have core := S196L_core A.prob hA.1 hA.2.1 P hP0 x
  have : A.prob x * S196L_val (fun _ : Bool => (1/2 : ℝ)) M
        (fun b => if b then ensembleMean A else A.state x) * Real.log 2 ≤
      S196L_val A.prob M A.state * Real.log 2 := by
    rw [mul_assoc, cB, cA]
    linarith
  exact le_of_mul_le_mul_right this hl

theorem S196L_triv [Nonempty E] : Nonempty (Measurement E) :=
  ⟨{ outcomes := 1
     positive := by decide
     effect := fun _ => 1
     valid := ⟨fun _ => Matrix.PosSemidef.one, by simp⟩ }⟩

theorem solution {m : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (A : CQData (Fin (2 ^ m)) E) (hA : A.Valid) :
    ∀ x, A.prob x * shannonDistinguishability (A.state x) (ensembleMean A) ≤
      accessibleInformation A := by
  intro x
  have e1 : shannonDistinguishability (A.state x) (ensembleMean A) =
      sSup {v | ∃ M : Measurement E, v = S196L_val (fun _ : Bool => (1/2 : ℝ)) M
        (fun b => if b then ensembleMean A else A.state x)} := rfl
  have e2 : accessibleInformation A =
      sSup {v | ∃ M : Measurement E, v = S196L_val A.prob M A.state} := rfl
  rw [e1, e2]
  obtain ⟨M0⟩ := S196L_triv (E := E)
  have hbdd : BddAbove {v | ∃ M : Measurement E, v = S196L_val A.prob M A.state} :=
    ⟨shannon A.prob, by rintro v ⟨M, rfl⟩; exact S196L_upper A hA M⟩
  rcases (hA.1 x).lt_or_eq with hp | hp
  · rw [mul_comm, ← le_div_iff₀ hp]
    refine csSup_le ⟨_, M0, rfl⟩ ?_
    rintro v ⟨M, rfl⟩
    rw [le_div_iff₀ hp, mul_comm]
    exact (S196L_pointwise A hA M x).trans (le_csSup hbdd ⟨M, rfl⟩)
  · rw [← hp, zero_mul]
    have h0 := S196L_pointwise A hA M0 x
    rw [← hp, zero_mul] at h0
    exact h0.trans (le_csSup hbdd ⟨M0, rfl⟩)

#print axioms solution
