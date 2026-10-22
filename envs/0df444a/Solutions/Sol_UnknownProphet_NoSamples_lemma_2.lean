-- Prove2me | solution 1 for UnknownProphet.NoSamples.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:31:49.749154+00:00
-- url     : https://prove2.me/submissions/ae5da919-dab8-4cf2-82ee-4872fe8c8b32

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples.SymAux

open Finset UnknownProphet.NoSamples

/-! ### Permutations of `Fin (m+1)` decomposed by the image of the last point -/

section Decomp

variable {m : ℕ}

def phiFun (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Fin (m + 1) → Fin (m + 1) :=
  Fin.lastCases a (fun j => a.succAbove (τ j))

lemma phiFun_last (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    phiFun a τ (Fin.last m) = a := by simp [phiFun]

lemma phiFun_castSucc (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    phiFun a τ (Fin.castSucc j) = a.succAbove (τ j) := by simp [phiFun]

lemma phiFun_inj (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Function.Injective (phiFun a τ) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast y =>
      rw [phiFun_last, phiFun_castSucc] at hxy
      exact absurd hxy.symm (Fin.succAbove_ne a _)
  | cast x =>
    induction y using Fin.lastCases with
    | last =>
      rw [phiFun_last, phiFun_castSucc] at hxy
      exact absurd hxy (Fin.succAbove_ne a _)
    | cast y =>
      rw [phiFun_castSucc, phiFun_castSucc] at hxy
      rw [τ.injective (Fin.succAbove_right_injective hxy)]

noncomputable def phi (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.ofBijective (phiFun a τ) (phiFun_inj a τ).bijective_of_finite

lemma phi_apply (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (x : Fin (m + 1)) :
    phi a τ x = phiFun a τ x := rfl

lemma phi_bij : Function.Bijective (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => phi p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨a, τ⟩ ⟨a', τ'⟩ h
    simp only at h
    have h1 : a = a' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ (Fin.last m)) h
      simp only [phi_apply, phiFun_last] at this
      exact this
    subst h1
    have h2 : τ = τ' := by
      ext j
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ (Fin.castSucc j)) h
      simp only [phi_apply, phiFun_castSucc] at this
      rw [Fin.succAbove_right_injective this]
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

lemma sum_perm_succ (f : Equiv.Perm (Fin (m + 1)) → ℝ) :
    ∑ σ, f σ = ∑ a : Fin (m + 1), ∑ τ : Equiv.Perm (Fin m), f (phi a τ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ phi_bij _ _ (fun p => rfl)).symm

lemma comp_phi (u : Fin (m + 1) → ℝ) (a : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    u ∘ phi a τ = (Fin.snoc ((u ∘ a.succAbove) ∘ τ) (u a) : Fin (m + 1) → ℝ) := by
  funext x
  induction x using Fin.lastCases with
  | last => simp [phi_apply, phiFun_last]
  | cast j => simp [phi_apply, phiFun_castSucc]

end Decomp

/-! ### Arrival probabilities and the symmetrised rule -/

variable {n : ℕ}

/-- Probability of reaching step `i` (zero-based) given the previous values `w`. -/
noncomputable def Arr (R : StoppingRule 0 n) (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ) : ℝ :=
  ∏ j : Fin i, (1 - R.r ⟨j, lt_of_lt_of_le j.isLt hi⟩ ![]
      (fun l : Fin (j + 1) => w ⟨l, lt_of_le_of_lt (Nat.le_of_lt_succ l.isLt) j.isLt⟩))

lemma Arr_nonneg (R : StoppingRule 0 n) (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ) :
    0 ≤ Arr R i hi w := by
  unfold Arr
  apply Finset.prod_nonneg
  intro j _
  linarith [(R.r_mem ⟨j, lt_of_lt_of_le j.isLt hi⟩ ![]
      (fun l : Fin (j + 1) => w ⟨l, lt_of_le_of_lt (Nat.le_of_lt_succ l.isLt) j.isLt⟩)).2]

lemma Arr_zero (R : StoppingRule 0 n) (hi : 0 ≤ n) (w : Fin 0 → ℝ) : Arr R 0 hi w = 1 := by
  simp [Arr]

lemma Arr_succ (R : StoppingRule 0 n) (i : ℕ) (hi : i + 1 ≤ n) (u : Fin (i + 1) → ℝ) :
    Arr R (i + 1) hi u = Arr R i (Nat.le_of_succ_le hi) (Fin.init u) *
      (1 - R.r ⟨i, hi⟩ ![] u) := by
  unfold Arr
  rw [Fin.prod_univ_castSucc]
  rfl

/-- Sum over the orders of the previous values of the arrival probability. -/
noncomputable def Dsum (R : StoppingRule 0 n) (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin i), Arr R i hi (w ∘ π)

/-- Sum over the orders of the previous values of the probability of stopping now. -/
noncomputable def Nsum (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin I.val), Arr R I.val I.isLt.le (w ∘ π) *
    R.r I ![] (Fin.snoc (w ∘ π) y : Fin (I.val + 1) → ℝ)

lemma Dsum_nonneg (R : StoppingRule 0 n) (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ) :
    0 ≤ Dsum R i hi w :=
  Finset.sum_nonneg (fun π _ => Arr_nonneg R i hi _)

lemma Nsum_nonneg (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) :
    0 ≤ Nsum R I w y :=
  Finset.sum_nonneg (fun π _ => mul_nonneg (Arr_nonneg R _ _ _) (R.r_mem _ _ _).1)

lemma Nsum_le (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) :
    Nsum R I w y ≤ Dsum R I.val I.isLt.le w := by
  apply Finset.sum_le_sum
  intro π _
  have h1 := Arr_nonneg R I.val I.isLt.le (w ∘ π)
  have h2 := (R.r_mem I ![] (Fin.snoc (w ∘ π) y : Fin (I.val + 1) → ℝ)).2
  nlinarith

noncomputable def symVal (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) : ℝ :=
  if Dsum R I.val I.isLt.le w = 0 then 0 else Nsum R I w y / Dsum R I.val I.isLt.le w

lemma symVal_mem (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) :
    symVal R I w y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold symVal
  split_ifs with h
  · exact ⟨le_refl 0, zero_le_one⟩
  · have hD : 0 < Dsum R I.val I.isLt.le w := lt_of_le_of_ne (Dsum_nonneg _ _ _ _) (Ne.symm h)
    exact ⟨div_nonneg (Nsum_nonneg _ _ _ _) hD.le,
      (div_le_one hD).mpr (Nsum_le _ _ _ _)⟩

lemma Nsum_eq (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) :
    Nsum R I w y = symVal R I w y * Dsum R I.val I.isLt.le w := by
  unfold symVal
  split_ifs with h
  · rw [zero_mul]
    apply le_antisymm _ (Nsum_nonneg _ _ _ _)
    rw [← h]; exact Nsum_le _ _ _ _
  · field_simp

/-- The symmetrised (order-oblivious) rule. -/
noncomputable def symR (R : StoppingRule 0 n) : StoppingRule 0 n where
  r I _ v := symVal R I (Fin.init v) (v (Fin.last I.val))
  r_mem I _ v := symVal_mem R I _ _

lemma symR_snoc (R : StoppingRule 0 n) (I : Fin n) (s : Fin 0 → ℝ) (w : Fin I.val → ℝ) (y : ℝ) :
    (symR R).r I s (Fin.snoc w y : Fin (I.val + 1) → ℝ) = symVal R I w y := by
  simp only [symR, Fin.init_snoc, Fin.snoc_last]

lemma Dsum_comp (R : StoppingRule 0 n) (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ)
    (ρ : Equiv.Perm (Fin i)) : Dsum R i hi (w ∘ ρ) = Dsum R i hi w := by
  unfold Dsum
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun π => Arr R i hi (w ∘ π))

lemma Nsum_comp (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ)
    (ρ : Equiv.Perm (Fin I.val)) : Nsum R I (w ∘ ρ) y = Nsum R I w y := by
  unfold Nsum
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun π => Arr R I.val I.isLt.le (w ∘ π) *
    R.r I ![] (Fin.snoc (w ∘ π) y : Fin (I.val + 1) → ℝ))

lemma symVal_comp (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ)
    (ρ : Equiv.Perm (Fin I.val)) : symVal R I (w ∘ ρ) y = symVal R I w y := by
  unfold symVal
  rw [Dsum_comp, Nsum_comp]

/-! ### Arrival invariance -/

lemma Dsum_symR (R : StoppingRule 0 n) :
    ∀ (i : ℕ) (hi : i ≤ n) (w : Fin i → ℝ), Dsum (symR R) i hi w = Dsum R i hi w := by
  intro i
  induction i with
  | zero =>
    intro hi w
    simp [Dsum, Arr_zero]
  | succ i ih =>
    intro hi u
    set I : Fin n := ⟨i, hi⟩
    have key : ∀ (R' : StoppingRule 0 n) (a : Fin (i + 1)),
        ∑ τ : Equiv.Perm (Fin i), Arr R' (i + 1) hi (u ∘ phi a τ) =
          ∑ τ : Equiv.Perm (Fin i), Arr R' i (Nat.le_of_succ_le hi) ((u ∘ a.succAbove) ∘ τ) *
            (1 - R'.r I ![] (Fin.snoc ((u ∘ a.succAbove) ∘ τ) (u a) : Fin (i + 1) → ℝ)) := by
      intro R' a
      apply Finset.sum_congr rfl
      intro τ _
      rw [comp_phi, Arr_succ, Fin.init_snoc]
    unfold Dsum
    rw [sum_perm_succ, sum_perm_succ]
    apply Finset.sum_congr rfl
    intro a _
    rw [key (symR R) a, key R a]
    -- symmetrised side
    have hs : ∀ τ : Equiv.Perm (Fin i),
        (symR R).r I ![] (Fin.snoc ((u ∘ a.succAbove) ∘ τ) (u a) : Fin (i + 1) → ℝ) =
          symVal R I (u ∘ a.succAbove) (u a) := by
      intro τ
      rw [symR_snoc]
      exact symVal_comp R I (u ∘ a.succAbove) (u a) τ
    simp_rw [hs]
    rw [← Finset.sum_mul]
    have h1 := ih (Nat.le_of_succ_le hi) (u ∘ a.succAbove)
    unfold Dsum at h1
    rw [h1]
    -- original side
    have e2 : ∑ τ : Equiv.Perm (Fin i), Arr R i (Nat.le_of_succ_le hi) ((u ∘ a.succAbove) ∘ τ) *
        (1 - R.r I ![] (Fin.snoc ((u ∘ a.succAbove) ∘ τ) (u a) : Fin (i + 1) → ℝ)) =
        Dsum R i (Nat.le_of_succ_le hi) (u ∘ a.succAbove) - Nsum R I (u ∘ a.succAbove) (u a) := by
      unfold Dsum Nsum
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    rw [e2, Nsum_eq]
    unfold Dsum
    ring


/-! ### Stopping probabilities in terms of arrival probabilities -/

/-- The first `I` observed values. -/
def pre (x : Fin n → ℝ) (I : Fin n) : Fin I.val → ℝ :=
  fun l => x ⟨l, lt_trans l.isLt I.isLt⟩

lemma castLE_eq_snoc (x : Fin n → ℝ) (I : Fin n) :
    x ∘ Fin.castLE (Nat.succ_le_of_lt I.isLt) =
      (Fin.snoc (pre x I) (x I) : Fin (I.val + 1) → ℝ) := by
  funext l
  induction l using Fin.lastCases with
  | last =>
    simp only [Function.comp_apply, Fin.snoc_last]
    congr 1
  | cast j =>
    simp only [Function.comp_apply, Fin.snoc_castSucc, pre]
    congr 1

lemma stopProb_eq (R : StoppingRule 0 n) (s : Fin 0 → ℝ) (x : Fin n → ℝ) (I : Fin n) :
    stopProb R s x I = Arr R I.val I.isLt.le (pre x I) *
      R.r I ![] (Fin.snoc (pre x I) (x I) : Fin (I.val + 1) → ℝ) := by
  have hs : s = ![] := Subsingleton.elim _ _
  subst hs
  unfold stopProb Arr
  rw [castLE_eq_snoc]
  congr 1
  exact Finset.prod_bij' (fun a ha => (⟨a.val, Fin.lt_def.mp (Finset.mem_Iio.mp ha)⟩ : Fin I.val))
    (fun b _ => (⟨b.val, lt_trans b.isLt I.isLt⟩ : Fin n))
    (fun a _ => Finset.mem_univ _)
    (fun b _ => Finset.mem_Iio.mpr (Fin.lt_def.mpr b.isLt))
    (fun a _ => rfl) (fun b _ => rfl) (fun a _ => rfl)

/-- Extension of a permutation of the first `I` positions to all positions. -/
def extFun (I : Fin n) (ρ : Equiv.Perm (Fin I.val)) : Fin n → Fin n :=
  fun j => if h : j.val < I.val then ⟨ρ ⟨j, h⟩, lt_trans (ρ ⟨j, h⟩).isLt I.isLt⟩ else j

lemma extFun_inj (I : Fin n) (ρ : Equiv.Perm (Fin I.val)) : Function.Injective (extFun I ρ) := by
  intro a b hab
  unfold extFun at hab
  split_ifs at hab with ha hb hb
  · have := congrArg Fin.val hab
    simp only at this
    have := ρ.injective (Fin.ext this)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · exfalso; apply hb
    have := congrArg Fin.val hab
    simp only at this
    rw [← this]; exact (ρ ⟨a, ha⟩).isLt
  · exfalso; apply ha
    have := congrArg Fin.val hab
    simp only at this
    rw [this]; exact (ρ ⟨b, hb⟩).isLt
  · exact hab

noncomputable def ext (I : Fin n) (ρ : Equiv.Perm (Fin I.val)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (extFun I ρ) (extFun_inj I ρ).bijective_of_finite

lemma pre_ext (x : Fin n → ℝ) (I : Fin n) (ρ : Equiv.Perm (Fin I.val)) :
    pre (x ∘ ext I ρ) I = pre x I ∘ ρ := by
  funext l
  simp only [pre, Function.comp_apply, ext, Equiv.ofBijective_apply, extFun, dif_pos l.isLt]

lemma ext_I (x : Fin n → ℝ) (I : Fin n) (ρ : Equiv.Perm (Fin I.val)) :
    (x ∘ ext I ρ) I = x I := by
  simp only [Function.comp_apply, ext, Equiv.ofBijective_apply, extFun, lt_irrefl, dif_neg,
    not_false_eq_true]

lemma sum_reindex (F : FinDist) (σ : Equiv.Perm (Fin n)) (g : (Fin n → ℝ) → ℝ) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), iidWeight F x * g x =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), iidWeight F x * g (x ∘ σ) := by
  symm
  apply Finset.sum_nbij' (fun x => x ∘ σ) (fun x => x ∘ ⇑σ⁻¹)
  · intro x hx
    simp only [Fintype.mem_piFinset] at hx ⊢
    intro i; exact hx _
  · intro x hx
    simp only [Fintype.mem_piFinset] at hx ⊢
    intro i; exact hx _
  · intro x _; funext i; simp
  · intro x _; funext i; simp
  · intro x _
    congr 1
    unfold iidWeight
    exact (Equiv.prod_comp σ (fun j => F.w (x j))).symm

/-- `I! ×` (contribution of index `I`) is the `Nsum`-weighted sum. -/
lemma contrib (F : FinDist) (R : StoppingRule 0 n) (I : Fin n) :
    (I.val.factorial : ℝ) * ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
        iidWeight F x * (stopProb R ![] x I * x I) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
        iidWeight F x * (Nsum R I (pre x I) (x I) * x I) := by
  set X := Fintype.piFinset (fun _ : Fin n => F.supp)
  have hcard : (Fintype.card (Equiv.Perm (Fin I.val)) : ℝ) = I.val.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  calc (I.val.factorial : ℝ) * ∑ x ∈ X, iidWeight F x * (stopProb R ![] x I * x I)
      = ∑ ρ : Equiv.Perm (Fin I.val), ∑ x ∈ X, iidWeight F x * (stopProb R ![] x I * x I) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ = ∑ ρ : Equiv.Perm (Fin I.val), ∑ x ∈ X, iidWeight F x *
          (Arr R I.val I.isLt.le (pre x I ∘ ρ) *
            R.r I ![] (Fin.snoc (pre x I ∘ ρ) (x I) : Fin (I.val + 1) → ℝ) * x I) := by
        apply Finset.sum_congr rfl
        intro ρ _
        rw [sum_reindex F (ext I ρ)]
        apply Finset.sum_congr rfl
        intro x _
        rw [stopProb_eq, pre_ext, ext_I]
    _ = ∑ x ∈ X, iidWeight F x * (Nsum R I (pre x I) (x I) * x I) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        unfold Nsum
        rw [Finset.sum_mul, Finset.mul_sum]

lemma Nsum_symR (R : StoppingRule 0 n) (I : Fin n) (w : Fin I.val → ℝ) (y : ℝ) :
    Nsum (symR R) I w y = Nsum R I w y := by
  have h1 : Nsum (symR R) I w y = Dsum (symR R) I.val I.isLt.le w * symVal R I w y := by
    unfold Nsum Dsum
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro π _
    rw [symR_snoc, symVal_comp]
  rw [h1, Dsum_symR, Nsum_eq, mul_comm]

lemma expStop_zero' (F : FinDist) (R : StoppingRule 0 n) :
    expStop F R = ∑ I : Fin n, ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * (stopProb R ![] x I * x I) := by
  unfold expStop
  have h0 : Fintype.piFinset (fun _ : Fin 0 => F.supp) = {![]} := by
    ext y
    simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [h0, Finset.sum_singleton]
  have h1 : iidWeight F (![] : Fin 0 → ℝ) = 1 := by simp [iidWeight]
  rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [one_mul, Finset.mul_sum]

lemma expStop_symR (F : FinDist) (R : StoppingRule 0 n) :
    expStop F (symR R) = expStop F R := by
  rw [expStop_zero', expStop_zero']
  apply Finset.sum_congr rfl
  intro I _
  have hf : (I.val.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  apply mul_left_cancel₀ hf
  rw [contrib, contrib]
  simp_rw [Nsum_symR]


/-! ### Order obliviousness and never-selected positions -/

lemma restrict_exists {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) (hπ : π (Fin.last m) = Fin.last m) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ j, π (Fin.castSucc j) = Fin.castSucc (ρ j) := by
  have hne : ∀ j : Fin m, π (Fin.castSucc j) ≠ Fin.last m := by
    intro j h
    rw [← hπ] at h
    exact (Fin.castSucc_lt_last j).ne (π.injective h)
  set f : Fin m → Fin m := fun j => (π (Fin.castSucc j)).castPred (hne j)
  have finj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := congrArg Fin.castSucc hab
    rw [Fin.castSucc_castPred, Fin.castSucc_castPred] at this
    exact Fin.castSucc_injective m (π.injective this)
  refine ⟨Equiv.ofBijective f finj.bijective_of_finite, fun j => ?_⟩
  simp only [Equiv.ofBijective_apply, f, Fin.castSucc_castPred]

lemma symR_orderOblivious (R : StoppingRule 0 n) : OrderOblivious (symR R) := by
  intro I v _ _ π hπ
  obtain ⟨ρ, hρ⟩ := restrict_exists π hπ
  have h1 : Fin.init (v ∘ π) = Fin.init v ∘ ρ := by
    funext j
    simp only [Fin.init, Function.comp_apply, hρ]
  have h2 : (v ∘ π) (Fin.last I.val) = v (Fin.last I.val) := by
    simp only [Function.comp_apply, hπ]
  show symVal R I (Fin.init (v ∘ π)) ((v ∘ π) (Fin.last I.val)) =
    symVal R I (Fin.init v) (v (Fin.last I.val))
  rw [h1, h2, symVal_comp]

lemma symR_neverSelects (R : StoppingRule 0 n) (I : Fin n) (h : NeverSelects R I) :
    NeverSelects (symR R) I := by
  intro s x hs hx
  rw [stopProb_eq, symR_snoc]
  have hN : Nsum R I (pre x I) (x I) = 0 := by
    unfold Nsum
    apply Finset.sum_eq_zero
    intro ρ _
    have := h ![] (x ∘ ext I ρ) (fun j => j.elim0) (fun j => hx _)
    rw [stopProb_eq, pre_ext, ext_I] at this
    exact this
  unfold symVal
  rw [hN]
  simp

end UnknownProphet.NoSamples.SymAux

open UnknownProphet.NoSamples UnknownProphet.NoSamples.SymAux in
theorem solution (n : ℕ) (α : ℝ) (R : StoppingRule 0 n)
    (hR : HasGuarantee R α) :
    ∃ R' : StoppingRule 0 n,
      HasGuarantee R' α ∧ OrderOblivious R' ∧
        ∀ i, NeverSelects R i → NeverSelects R' i := by
  refine ⟨symR R, ?_, symR_orderOblivious R, fun i hi => symR_neverSelects R i hi⟩
  intro F
  rw [expStop_symR]
  exact hR F
