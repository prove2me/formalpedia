-- Prove2me | solution 1 for RadGauss.Structural.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:28:05.204052+00:00
-- url     : https://prove2.me/submissions/534be619-1355-4796-b636-6c462b8c6409

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

namespace RG12Aux

open RadGauss.RiskBound

lemma signVal_not (b : Bool) : signVal (!b) = - signVal b := by
  cases b <;> simp [signVal]

lemma signVal_cases (b : Bool) : signVal b = 1 ∨ signVal b = -1 := by
  cases b <;> simp [signVal]

lemma abs_signVal (b : Bool) : |signVal b| = 1 := by
  cases b <;> simp [signVal]

/-- swap lemma: replacing coordinate `j` by a less-contracted one does not decrease. -/
lemma swap_le {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (v v' : ι → Fin n → ℝ) (j : Fin n)
    (hv : ∀ a i, i ≠ j → v a i = v' a i)
    (hj : ∀ a b, |v a j - v b j| ≤ |v' a j - v' b j|) :
    ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * v a i ≤
      ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * v' a i := by
  classical
  set fl : (Fin n → Bool) → (Fin n → Bool) := fun σ => Function.update σ j (!σ j) with hfl
  have hinv : Function.Involutive fl := by
    intro σ
    funext i
    by_cases h : i = j
    · subst h; simp [hfl]
    · simp [hfl, Function.update_of_ne h]
  have hsum : ∀ G : (Fin n → Bool) → ℝ, ∑ σ, G σ = ∑ σ, G (fl σ) := by
    intro G
    exact (Fintype.sum_equiv hinv.toPerm _ _ (fun σ => rfl)).symm
  -- decomposition of sums
  have hdec : ∀ (w : ι → Fin n → ℝ) (σ : Fin n → Bool) a,
      ∑ i, signVal (σ i) * w a i =
        signVal (σ j) * w a j + ∑ i ∈ Finset.univ.erase j, signVal (σ i) * w a i := by
    intro w σ a
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hR : ∀ (σ : Fin n → Bool) a,
      ∑ i ∈ Finset.univ.erase j, signVal (fl σ i) * v a i =
        ∑ i ∈ Finset.univ.erase j, signVal (σ i) * v' a i ∧
      ∑ i ∈ Finset.univ.erase j, signVal (σ i) * v a i =
        ∑ i ∈ Finset.univ.erase j, signVal (σ i) * v' a i ∧
      ∑ i ∈ Finset.univ.erase j, signVal (fl σ i) * v' a i =
        ∑ i ∈ Finset.univ.erase j, signVal (σ i) * v' a i := by
    intro σ a
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [hfl, Function.update_of_ne hij, hv a i hij]
  have hflj : ∀ σ, signVal (fl σ j) = - signVal (σ j) := by
    intro σ; simp [hfl, signVal_not]
  set G : (ι → Fin n → ℝ) → (Fin n → Bool) → ℝ :=
    fun w σ => ⨆ a, ∑ i, signVal (σ i) * w a i with hG
  have hle : ∀ (w : ι → Fin n → ℝ) σ a, ∑ i, signVal (σ i) * w a i ≤ G w σ := by
    intro w σ a
    exact le_ciSup (f := fun a => ∑ i, signVal (σ i) * w a i) (Finite.bddAbove_range _) a
  have key : ∀ σ, G v σ + G v (fl σ) ≤ G v' σ + G v' (fl σ) := by
    intro σ
    have h1 : ∀ a b, ∑ i, signVal (σ i) * v a i + ∑ i, signVal (fl σ i) * v b i ≤
        G v' σ + G v' (fl σ) := by
      intro a b
      rw [hdec v σ a, hdec v (fl σ) b, (hR σ a).2.1, (hR σ b).1, hflj]
      have e1 := hle v' σ a
      have e2 := hle v' (fl σ) b
      have e3 := hle v' σ b
      have e4 := hle v' (fl σ) a
      rw [hdec v' σ a] at e1
      rw [hdec v' (fl σ) b, (hR σ b).2.2, hflj] at e2
      rw [hdec v' σ b] at e3
      rw [hdec v' (fl σ) a, (hR σ a).2.2, hflj] at e4
      have hab := hj a b
      rcases signVal_cases (σ j) with hs | hs <;> rw [hs] at e1 e2 e3 e4 ⊢ <;>
      · rcases abs_cases (v a j - v b j) with ⟨h5, _⟩ | ⟨h5, _⟩ <;>
        rcases abs_cases (v' a j - v' b j) with ⟨h6, _⟩ | ⟨h6, _⟩ <;>
        · rw [h5, h6] at hab
          linarith
    have h2 : ∀ a, ∑ i, signVal (σ i) * v a i + G v (fl σ) ≤ G v' σ + G v' (fl σ) := by
      intro a
      have : G v (fl σ) ≤ G v' σ + G v' (fl σ) - ∑ i, signVal (σ i) * v a i := by
        apply ciSup_le
        intro b
        have := h1 a b
        linarith
      linarith
    have : G v σ ≤ G v' σ + G v' (fl σ) - G v (fl σ) := by
      apply ciSup_le
      intro a
      have := h2 a
      linarith
    linarith
  have A : ∑ σ, G v σ + ∑ σ, G v σ = ∑ σ, (G v σ + G v (fl σ)) := by
    rw [Finset.sum_add_distrib, ← hsum (G v)]
  have B : ∑ σ, G v' σ + ∑ σ, G v' σ = ∑ σ, (G v' σ + G v' (fl σ)) := by
    rw [Finset.sum_add_distrib, ← hsum (G v')]
  have C : ∑ σ, (G v σ + G v (fl σ)) ≤ ∑ σ, (G v' σ + G v' (fl σ)) :=
    Finset.sum_le_sum fun σ _ => key σ
  show ∑ σ, G v σ ≤ ∑ σ, G v' σ
  linarith

/-- contraction comparison without absolute values. -/
lemma contraction {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → Fin n → ℝ)
    (φ : ℝ → ℝ) (L : NNReal) (hφ : LipschitzWith L φ) :
    ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * φ (u a i) ≤
      (L : ℝ) * ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * u a i := by
  classical
  let w : Finset (Fin n) → ι → Fin n → ℝ :=
    fun S a i => if i ∈ S then (L : ℝ) * u a i else φ (u a i)
  let Q : Finset (Fin n) → ℝ := fun S => ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * w S a i
  have hmono : ∀ S : Finset (Fin n), Q ∅ ≤ Q S := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact le_rfl
    | insert j S hj ih =>
      refine ih.trans ?_
      apply swap_le (w S) (w (insert j S)) j
      · intro a i hij
        simp [w, Finset.mem_insert, hij]
      · intro a b
        simp only [w, Finset.mem_insert_self, if_true, hj, if_false]
        have := hφ.dist_le_mul (u a j) (u b j)
        rw [Real.dist_eq, Real.dist_eq] at this
        rw [← mul_sub, abs_mul, abs_of_nonneg (NNReal.coe_nonneg L)]
        exact this
  have h0 : Q ∅ = ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * φ (u a i) := by
    simp [Q, w]
  have h1 : Q Finset.univ = (L : ℝ) * ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * u a i := by
    simp only [Q, w, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Real.mul_iSup_of_nonneg (NNReal.coe_nonneg L)]
    congr 1
    funext a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← h0, ← h1]
  exact hmono Finset.univ

/-- core real contraction with absolute values. -/
lemma core {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → Fin n → ℝ)
    (φ : ℝ → ℝ) (L : NNReal) (hφ : LipschitzWith L φ) (hφ0 : φ 0 = 0)
    (a0 : ι) (ha0 : ∀ i, u a0 i = 0) :
    ∑ σ : Fin n → Bool, ⨆ a, |∑ i, signVal (σ i) * φ (u a i)| ≤
      2 * (L : ℝ) * ∑ σ : Fin n → Bool, ⨆ a, |∑ i, signVal (σ i) * u a i| := by
  classical
  set S : (Fin n → Bool) → ι → ℝ := fun σ a => ∑ i, signVal (σ i) * φ (u a i) with hS
  have hneg : ∀ σ a, S (fun i => !σ i) a = - S σ a := by
    intro σ a
    simp only [hS, signVal_not, neg_mul, Finset.sum_neg_distrib]
  have hz : ∀ σ, S σ a0 = 0 := by
    intro σ; simp [hS, ha0, hφ0]
  have stepA : ∀ σ, ⨆ a, |S σ a| ≤ (⨆ a, S σ a) + ⨆ a, S (fun i => !σ i) a := by
    intro σ
    apply ciSup_le
    intro a
    have e1 : S σ a ≤ ⨆ a, S σ a := le_ciSup (Finite.bddAbove_range _) a
    have e2 : S (fun i => !σ i) a ≤ ⨆ a, S (fun i => !σ i) a :=
      le_ciSup (Finite.bddAbove_range _) a
    have e3 : S σ a0 ≤ ⨆ a, S σ a := le_ciSup (Finite.bddAbove_range _) a0
    have e4 : S (fun i => !σ i) a0 ≤ ⨆ a, S (fun i => !σ i) a :=
      le_ciSup (Finite.bddAbove_range _) a0
    rw [hz] at e3 e4
    rw [hneg] at e2
    rcases abs_cases (S σ a) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have stepB : ∑ σ : Fin n → Bool, ⨆ a, S (fun i => !σ i) a =
      ∑ σ : Fin n → Bool, ⨆ a, S σ a := by
    have hinv : Function.Involutive (fun σ : Fin n → Bool => fun i => !σ i) := by
      intro σ; funext i; simp
    exact Fintype.sum_equiv hinv.toPerm _ _ (fun σ => rfl)
  have stepC := contraction u φ L hφ
  have stepD : ∀ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * u a i ≤
      ⨆ a, |∑ i, signVal (σ i) * u a i| := by
    intro σ
    apply ciSup_mono (Finite.bddAbove_range _)
    intro a
    exact le_abs_self _
  have hD : ∑ σ : Fin n → Bool, ⨆ a, ∑ i, signVal (σ i) * u a i ≤
      ∑ σ : Fin n → Bool, ⨆ a, |∑ i, signVal (σ i) * u a i| :=
    Finset.sum_le_sum fun σ _ => stepD σ
  have hA : ∑ σ : Fin n → Bool, ⨆ a, |S σ a| ≤
      ∑ σ : Fin n → Bool, ((⨆ a, S σ a) + ⨆ a, S (fun i => !σ i) a) :=
    Finset.sum_le_sum fun σ _ => stepA σ
  rw [Finset.sum_add_distrib, stepB] at hA
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have := mul_le_mul_of_nonneg_left hD hL
  show ∑ σ : Fin n → Bool, ⨆ a, |S σ a| ≤ _
  nlinarith


lemma emp_mono {Z : Type*} (n : ℕ) {F H : Set (Z → ℝ)} (h : F ⊆ H) (x : Fin n → Z) :
    empiricalRademacher n F x ≤ empiricalRademacher n H x := by
  unfold empiricalRademacher
  exact mul_le_mul_right (Finset.sum_le_sum fun σ _ => biSup_mono h) _

lemma emp_absconv_le {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (x : Fin n → Z) :
    empiricalRademacher n (convexHull ℝ (F ∪ -F)) x ≤ empiricalRademacher n F x := by
  unfold empiricalRademacher
  refine mul_le_mul_right (Finset.sum_le_sum fun σ _ => ?_) _
  set c : ℝ := 2 / (n : ℝ)
  set M := ⨆ g ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)| with hMdef
  by_cases hM : M = ⊤
  · rw [hM]; exact le_top
  set m := M.toReal
  have hK : ∀ g ∈ F ∪ -F, |c * ∑ i, signVal (σ i) * g (x i)| ≤ m := by
    rintro g (hg | hg)
    · have := le_iSup₂ (f := fun g (_ : g ∈ F) =>
        ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)|) g hg
      exact (ENNReal.ofReal_le_iff_le_toReal hM).1 this
    · rw [Set.mem_neg] at hg
      have := le_iSup₂ (f := fun g (_ : g ∈ F) =>
        ENNReal.ofReal |c * ∑ i, signVal (σ i) * g (x i)|) (-g) hg
      have h2 := (ENNReal.ofReal_le_iff_le_toReal hM).1 this
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, abs_neg] at h2
      exact h2
  have hconv : Convex ℝ {g : Z → ℝ | |c * ∑ i, signVal (σ i) * g (x i)| ≤ m} := by
    intro g1 hg1 g2 hg2 a b ha hb hab
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hg1 hg2 ⊢
    have e : c * ∑ i, signVal (σ i) * (a * g1 (x i) + b * g2 (x i)) =
        a * (c * ∑ i, signVal (σ i) * g1 (x i)) + b * (c * ∑ i, signVal (σ i) * g2 (x i)) := by
      have hi : ∀ i, signVal (σ i) * (a * g1 (x i) + b * g2 (x i)) =
          a * (signVal (σ i) * g1 (x i)) + b * (signVal (σ i) * g2 (x i)) := fun i => by ring
      simp_rw [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [e]
    calc |a * (c * ∑ i, signVal (σ i) * g1 (x i)) + b * (c * ∑ i, signVal (σ i) * g2 (x i))|
        ≤ |a * (c * ∑ i, signVal (σ i) * g1 (x i))| + |b * (c * ∑ i, signVal (σ i) * g2 (x i))| :=
          abs_add_le _ _
      _ = a * |c * ∑ i, signVal (σ i) * g1 (x i)| + b * |c * ∑ i, signVal (σ i) * g2 (x i)| := by
          rw [abs_mul a, abs_mul b, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * m + b * m := by gcongr
      _ = m := by rw [← add_mul, hab, one_mul]
  have hsub := convexHull_min (fun g hg => hK g hg) hconv
  apply iSup₂_le
  intro g hg
  exact (ENNReal.ofReal_le_iff_le_toReal hM).2 (hsub hg)

lemma emp_smul {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (c : ℝ) (x : Fin n → Z) :
    empiricalRademacher n (c • F) x = ENNReal.ofReal |c| * empiricalRademacher n F x := by
  unfold empiricalRademacher
  rw [mul_left_comm (ENNReal.ofReal |c|)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Set.image_smul, iSup_image, ENNReal.mul_iSup]
  congr 1
  funext g
  rw [ENNReal.mul_iSup]
  congr 1
  funext _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul]
  congr 2
  have : ∑ i, signVal (σ i) * (c * g (x i)) = c * ∑ i, signVal (σ i) * g (x i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

lemma fin_part {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (φ : ℝ → ℝ) (L : NNReal)
    (hφ : LipschitzWith L φ) (hφ0 : φ 0 = 0) (x : Fin n → Z) (c : ℝ)
    (g : (Fin n → Bool) → F) :
    ∑ σ : Fin n → Bool, ENNReal.ofReal |c * ∑ i, signVal (σ i) * φ ((g σ : Z → ℝ) (x i))| ≤
      2 * (L : ℝ≥0∞) * ∑ σ : Fin n → Bool,
        ⨆ f ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * f (x i)| := by
  let u : Option (Fin n → Bool) → Fin n → ℝ :=
    fun o i => Option.elim o 0 (fun τ => ((g τ : F) : Z → ℝ) (x i))
  have hcore := core u φ L hφ hφ0 none (fun i => rfl)
  let Mφ : (Fin n → Bool) → ℝ := fun σ => ⨆ o, |∑ i, signVal (σ i) * φ (u o i)|
  let N : (Fin n → Bool) → ℝ := fun σ => ⨆ o, |∑ i, signVal (σ i) * u o i|
  change ∑ σ : Fin n → Bool, Mφ σ ≤ 2 * (L : ℝ) * ∑ σ : Fin n → Bool, N σ at hcore
  have hMφ0 : ∀ σ, 0 ≤ Mφ σ := fun σ =>
    (abs_nonneg _).trans (le_ciSup (f := fun o => |∑ i, signVal (σ i) * φ (u o i)|)
      (Finite.bddAbove_range _) none)
  have hN0 : ∀ σ, 0 ≤ N σ := fun σ =>
    (abs_nonneg _).trans (le_ciSup (f := fun o => |∑ i, signVal (σ i) * u o i|)
      (Finite.bddAbove_range _) none)
  have step1 : ∀ σ, ENNReal.ofReal |c * ∑ i, signVal (σ i) * φ ((g σ : Z → ℝ) (x i))| ≤
      ENNReal.ofReal (|c| * Mφ σ) := by
    intro σ
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
    exact le_ciSup (f := fun o => |∑ i, signVal (σ i) * φ (u o i)|)
      (Finite.bddAbove_range _) (some σ)
  have step2 : ∀ σ, ENNReal.ofReal (|c| * N σ) ≤
      ⨆ f ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * f (x i)| := by
    intro σ
    obtain ⟨o, ho⟩ := exists_eq_ciSup_of_finite (f := fun o => |∑ i, signVal (σ i) * u o i|)
    have hNo : N σ = |∑ i, signVal (σ i) * u o i| := ho.symm
    rw [hNo]
    cases o with
    | none =>
      have : ∀ i, u none i = 0 := fun i => rfl
      simp only [this, mul_zero, Finset.sum_const_zero, abs_zero, ENNReal.ofReal_zero]
      exact bot_le
    | some τ =>
      refine le_iSup₂_of_le ((g τ : F) : Z → ℝ) (g τ).2 ?_
      rw [← abs_mul]
      exact le_rfl
  have hsum1 : ∑ σ : Fin n → Bool, ENNReal.ofReal (|c| * Mφ σ) =
      ENNReal.ofReal (∑ σ : Fin n → Bool, |c| * Mφ σ) :=
    (ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg (abs_nonneg c) (hMφ0 σ)).symm
  have hsum2 : ENNReal.ofReal (2 * (L : ℝ) * ∑ σ : Fin n → Bool, |c| * N σ) =
      2 * (L : ℝ≥0∞) * ∑ σ : Fin n → Bool, ENNReal.ofReal (|c| * N σ) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg (abs_nonneg c) (hN0 σ)]
  have hmid : ∑ σ : Fin n → Bool, |c| * Mφ σ ≤ 2 * (L : ℝ) * ∑ σ : Fin n → Bool, |c| * N σ := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hcore (abs_nonneg c)
    linarith
  calc ∑ σ : Fin n → Bool, ENNReal.ofReal |c * ∑ i, signVal (σ i) * φ ((g σ : Z → ℝ) (x i))|
      ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (|c| * Mφ σ) := Finset.sum_le_sum fun σ _ => step1 σ
    _ = ENNReal.ofReal (∑ σ : Fin n → Bool, |c| * Mφ σ) := hsum1
    _ ≤ ENNReal.ofReal (2 * (L : ℝ) * ∑ σ : Fin n → Bool, |c| * N σ) :=
        ENNReal.ofReal_le_ofReal hmid
    _ = 2 * (L : ℝ≥0∞) * ∑ σ : Fin n → Bool, ENNReal.ofReal (|c| * N σ) := hsum2
    _ ≤ 2 * (L : ℝ≥0∞) * ∑ σ : Fin n → Bool,
          ⨆ f ∈ F, ENNReal.ofReal |c * ∑ i, signVal (σ i) * f (x i)| :=
        mul_le_mul_right (Finset.sum_le_sum fun σ _ => step2 σ) _

lemma sum_sup_le {Z : Type*} (n : ℕ) (F : Set (Z → ℝ))
    (h : (Fin n → Bool) → (Z → ℝ) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ g : (Fin n → Bool) → F, ∑ σ : Fin n → Bool, h σ (g σ) ≤ C) :
    ∑ σ : Fin n → Bool, ⨆ f ∈ F, h σ f ≤ C := by
  classical
  have hsub : ∀ σ : Fin n → Bool, (⨆ f ∈ F, h σ f) =
      ⨆ g : (Fin n → Bool) → F, h σ (g σ : Z → ℝ) := by
    intro σ
    rw [iSup_subtype']
    exact (Function.Surjective.iSup_comp (f := fun g : (Fin n → Bool) → F => g σ)
      (fun p => ⟨fun _ => p, rfl⟩) (fun p : F => h σ (p : Z → ℝ))).symm
  have hdir : ∀ g1 g2 : (Fin n → Bool) → F, ∃ k : (Fin n → Bool) → F, ∀ σ,
      h σ (g1 σ) ≤ h σ (k σ) ∧ h σ (g2 σ) ≤ h σ (k σ) := by
    intro g1 g2
    refine ⟨fun σ => if h σ (g1 σ) ≤ h σ (g2 σ) then g2 σ else g1 σ, fun σ => ?_⟩
    by_cases hc : h σ (g1 σ) ≤ h σ (g2 σ)
    · dsimp only; rw [if_pos hc]; exact ⟨hc, le_rfl⟩
    · dsimp only; rw [if_neg hc]; exact ⟨le_rfl, le_of_not_ge hc⟩
  have hswap : ∑ σ : Fin n → Bool, ⨆ g : (Fin n → Bool) → F, h σ (g σ : Z → ℝ) =
      ⨆ g : (Fin n → Bool) → F, ∑ σ, h σ (g σ : Z → ℝ) :=
    ENNReal.finsetSum_iSup (f := fun (σ : Fin n → Bool) (g : (Fin n → Bool) → F) => h σ (g σ : Z → ℝ)) hdir
  rw [Finset.sum_congr rfl fun σ _ => hsub σ, hswap]
  exact iSup_le hC

lemma emp_contr {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (φ : ℝ → ℝ) (L : NNReal)
    (hφ : LipschitzWith L φ) (hφ0 : φ 0 = 0) (x : Fin n → Z) :
    empiricalRademacher n ((fun f => φ ∘ f) '' F) x ≤
      2 * (L : ℝ≥0∞) * empiricalRademacher n F x := by
  unfold empiricalRademacher
  rw [mul_left_comm (2 * (L : ℝ≥0∞))]
  refine mul_le_mul_right ?_ _
  have hL : ∀ σ : Fin n → Bool, (⨆ f ∈ (fun f => φ ∘ f) '' F,
      ENNReal.ofReal |2 / (n : ℝ) * ∑ i, signVal (σ i) * f (x i)|) =
      ⨆ f ∈ F, ENNReal.ofReal |2 / (n : ℝ) * ∑ i, signVal (σ i) * φ (f (x i))| := by
    intro σ
    rw [iSup_image]
    rfl
  rw [Finset.sum_congr rfl fun σ _ => hL σ]
  exact sum_sup_le n F (fun σ f => ENNReal.ofReal |2 / (n : ℝ) * ∑ i, signVal (σ i) * φ (f (x i))|)
    _ (fin_part n F φ L hφ hφ0 x (2 / (n : ℝ)))

lemma emp_sum {Z : Type*} (n k : ℕ) (Fs : Fin k → Set (Z → ℝ)) (x : Fin n → Z) :
    empiricalRademacher n (∑ l, Fs l) x ≤ ∑ l, empiricalRademacher n (Fs l) x := by
  unfold empiricalRademacher
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun σ _ => ?_
  set c : ℝ := 2 / (n : ℝ)
  apply iSup₂_le
  intro f hf
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hf
  have e : c * ∑ i, signVal (σ i) * (∑ l, g l) (x i) =
      ∑ l, c * ∑ i, signVal (σ i) * g l (x i) := by
    simp_rw [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  calc ENNReal.ofReal |c * ∑ i, signVal (σ i) * (∑ l, g l) (x i)|
      ≤ ENNReal.ofReal (∑ l, |c * ∑ i, signVal (σ i) * g l (x i)|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [e]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, ENNReal.ofReal |c * ∑ i, signVal (σ i) * g l (x i)| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑ l, ⨆ f ∈ Fs l, ENNReal.ofReal |c * ∑ i, signVal (σ i) * f (x i)| :=
        Finset.sum_le_sum fun l _ => le_iSup₂_of_le (g l) (hg (Finset.mem_univ l)) le_rfl

end RG12Aux

open MeasureTheory ENNReal Pointwise in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (∀ F H : Set (X → ℝ), F ⊆ H → RadGauss.RiskBound.rademacherComplexity μ n F ≤ RadGauss.RiskBound.rademacherComplexity μ n H) ∧
    (∀ F : Set (X → ℝ),
      RadGauss.RiskBound.rademacherComplexity μ n F = RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) ∧
        RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) =
          RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ (F ∪ -F))) ∧
    (∀ (F : Set (X → ℝ)) (c : ℝ),
      RadGauss.RiskBound.rademacherComplexity μ n (c • F) = ENNReal.ofReal |c| * RadGauss.RiskBound.rademacherComplexity μ n F) ∧
    (∀ (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal), LipschitzWith Lφ φ → φ 0 = 0 →
      RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
        2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F) ∧
    (∀ (k : ℕ) (Fs : Fin k → Set (X → ℝ)),
      (∀ i, AEMeasurable (RadGauss.RiskBound.empiricalRademacher n (Fs i)) (Measure.pi fun _ : Fin n => μ)) →
      RadGauss.RiskBound.rademacherComplexity μ n (∑ i, Fs i) ≤ ∑ i, RadGauss.RiskBound.rademacherComplexity μ n (Fs i)) := by
  have mono : ∀ F H : Set (X → ℝ), F ⊆ H → RadGauss.RiskBound.rademacherComplexity μ n F ≤
      RadGauss.RiskBound.rademacherComplexity μ n H := by
    intro F H hFH
    exact lintegral_mono fun x => RG12Aux.emp_mono n hFH x
  refine ⟨mono, ?_, ?_, ?_, ?_⟩
  · intro F
    have h1 := mono F (convexHull ℝ F) (subset_convexHull ℝ F)
    have h2 := mono (convexHull ℝ F) (convexHull ℝ (F ∪ -F))
      (convexHull_mono Set.subset_union_left)
    have h3 : RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ (F ∪ -F)) ≤
        RadGauss.RiskBound.rademacherComplexity μ n F :=
      lintegral_mono fun x => RG12Aux.emp_absconv_le n F x
    exact ⟨le_antisymm h1 (h2.trans h3), le_antisymm h2 (h3.trans h1)⟩
  · intro F c
    unfold RadGauss.RiskBound.rademacherComplexity
    simp_rw [RG12Aux.emp_smul]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · intro F φ Lφ hφ hφ0
    unfold RadGauss.RiskBound.rademacherComplexity
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)]
    exact lintegral_mono fun x => RG12Aux.emp_contr n F φ Lφ hφ hφ0 x
  · intro k Fs hF
    unfold RadGauss.RiskBound.rademacherComplexity
    rw [← lintegral_finsetSum' _ fun i _ => hF i]
    exact lintegral_mono fun x => RG12Aux.emp_sum n k Fs x
