-- Prove2me | solution 1 for UnknownProphet.NoSamples.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:38:41.068807+00:00
-- url     : https://prove2.me/submissions/710d4c6f-b417-44f8-aea4-8a8aecb08bee

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model
import Theorems.Thm_UnknownProphet_NoSamples_lemma_3

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


namespace UnknownProphet.NoSamples.Lemma1Aux

open Finset UnknownProphet.NoSamples UnknownProphet.NoSamples.SymAux

/-! ### General symmetry of the symmetrised rule -/

lemma symR_symm {N : ℕ} (R : StoppingRule 0 N) (I : Fin N) (v : Fin (I.val + 1) → ℝ)
    (π : Equiv.Perm (Fin (I.val + 1))) (hπ : π (Fin.last I.val) = Fin.last I.val) :
    (symR R).r I ![] (v ∘ π) = (symR R).r I ![] v := by
  obtain ⟨ρ, hρ⟩ := restrict_exists π hπ
  have h1 : Fin.init (v ∘ π) = Fin.init v ∘ ρ := by
    funext j
    simp only [Fin.init, Function.comp_apply, hρ]
  have h2 : (v ∘ π) (Fin.last I.val) = v (Fin.last I.val) := by
    simp only [Function.comp_apply, hπ]
  show symVal R I (Fin.init (v ∘ π)) ((v ∘ π) (Fin.last I.val)) =
    symVal R I (Fin.init v) (v (Fin.last I.val))
  rw [h1, h2, symVal_comp]

/-! ### Ramsey: value obliviousness of a symmetric rule -/

/-- The one-index property: on records with values in `V` the stop probability at `l`
is within `ε` of `ql`. -/
def GoodAt {N : ℕ} (S : StoppingRule 0 N) (ε : ℝ) (V : Set ℕ) (l : Fin N) (ql : ℝ) : Prop :=
  ql ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ u : Fin (l.val + 1) → ℕ, (∀ j, u j ∈ V) → Function.Injective u →
      (∀ j, j ≠ Fin.last l.val → u j < u (Fin.last l.val)) →
        S.r l ![] (fun j => (u j : ℝ)) ∈ Set.Ico (ql - ε) (ql + ε)

lemma GoodAt_mono {N : ℕ} (S : StoppingRule 0 N) (ε : ℝ) (V V' : Set ℕ) (h : V' ⊆ V)
    (l : Fin N) (ql : ℝ) (hg : GoodAt S ε V l ql) : GoodAt S ε V' l ql :=
  ⟨hg.1, fun u hu hinj hrec => hg.2 u (fun j => h (hu j)) hinj hrec⟩

lemma bucket_spec (ε t : ℝ) (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (b : ℕ)
    (hb : ⌊t / (2 * ε)⌋₊ = b) :
    t ∈ Set.Ico (min ((2 * b + 1) * ε) 1 - ε) (min ((2 * b + 1) * ε) 1 + ε) := by
  have h2e : 0 < 2 * ε := by linarith
  have hlo : (b : ℝ) ≤ t / (2 * ε) := by
    rw [← hb]; exact Nat.floor_le (div_nonneg ht0 h2e.le)
  have hhi : t / (2 * ε) < b + 1 := by
    rw [← hb]; exact Nat.lt_floor_add_one _
  rw [le_div_iff₀ h2e] at hlo
  rw [div_lt_iff₀ h2e] at hhi
  constructor
  · have : min ((2 * b + 1) * ε) 1 ≤ (2 * b + 1) * ε := min_le_left _ _
    nlinarith
  · rcases le_total ((2 * b + 1) * ε) 1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; linarith

lemma ramsey_step {N : ℕ} (S : StoppingRule 0 N)
    (hsym : ∀ (I : Fin N) (v : Fin (I.val + 1) → ℝ) (π : Equiv.Perm (Fin (I.val + 1))),
      π (Fin.last I.val) = Fin.last I.val → S.r I ![] (v ∘ π) = S.r I ![] v)
    (ε : ℝ) (hε : 0 < ε) (W : Set ℕ) (hW : W.Infinite) (l : Fin N) :
    ∃ U : Set ℕ, U ⊆ W ∧ U.Infinite ∧ ∃ ql : ℝ, GoodAt S ε U l ql := by
  classical
  set C : ℕ := ⌊1 / (2 * ε)⌋₊ + 1
  have hC : 0 < C := Nat.succ_pos _
  set val : Finset ℕ → ℝ := fun A =>
    if h : A.card = l.val + 1 then S.r l ![] (fun j => ((A.orderEmbOfFin h j : ℕ) : ℝ)) else 0
  set χ : Finset ℕ → Fin C := fun A => ⟨min ⌊val A / (2 * ε)⌋₊ (C - 1), by omega⟩
  obtain ⟨U, hUW, hUinf, col, hcol⟩ := lemma_3 C (l.val + 1) hC (Nat.succ_pos _) W hW χ
  refine ⟨U, hUW, hUinf, min ((2 * (col : ℕ) + 1) * ε) 1, ?_, ?_⟩
  · constructor
    · apply le_min (by positivity) zero_le_one
    · exact min_le_right _ _
  · intro u hu hinj hrec
    set A : Finset ℕ := Finset.univ.image u
    have hA : A.card = l.val + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hAU : (A : Set ℕ) ⊆ U := by
      intro a ha
      simp only [A, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha
      obtain ⟨j, rfl⟩ := ha
      exact hu j
    -- sorting permutation
    set σ := Tuple.sort u
    have hsm : StrictMono (u ∘ σ) :=
      (Tuple.monotone_sort u).strictMono_of_injective (hinj.comp σ.injective)
    have hsorted : (u ∘ σ) = fun j => (A.orderEmbOfFin hA j : ℕ) := by
      apply Finset.orderEmbOfFin_unique hA
      · intro j; simp [A]
      · exact hsm
    have hσlast : σ (Fin.last l.val) = Fin.last l.val := by
      have hle : ∀ j, u j ≤ u (Fin.last l.val) := by
        intro j
        by_cases hj : j = Fin.last l.val
        · rw [hj]
        · exact (hrec j hj).le
      by_contra hne
      have h1 : u (σ (Fin.last l.val)) < u (Fin.last l.val) := by
        apply lt_of_le_of_ne (hle _)
        intro e; exact hne (hinj e)
      -- the preimage of `last` under σ sits at some index ≤ last
      have h2 : u (σ (σ.symm (Fin.last l.val))) ≤ u (σ (Fin.last l.val)) :=
        hsm.monotone (Fin.le_last _)
      simp only [Equiv.apply_symm_apply] at h2
      exact absurd h1 (not_lt.mpr h2)
    have hval : S.r l ![] (fun j => (u j : ℝ)) = val A := by
      simp only [val, dif_pos hA]
      rw [← hsym l (fun j => (u j : ℝ)) σ hσlast]
      congr 1
      funext j
      have := congrFun hsorted j
      simp only [Function.comp_apply] at this ⊢
      rw [this]
    have ht := S.r_mem l ![] (fun j => (u j : ℝ))
    rw [hval] at ht ⊢
    have hχ := hcol A hAU hA
    have hfl : ⌊val A / (2 * ε)⌋₊ ≤ C - 1 := by
      simp only [C, Nat.add_sub_cancel]
      apply Nat.floor_le_floor
      apply div_le_div_of_nonneg_right ht.2 (by linarith)
    have hb : ⌊val A / (2 * ε)⌋₊ = (col : ℕ) := by
      have := congrArg Fin.val hχ
      simp only [χ] at this
      rw [min_eq_left hfl] at this
      exact this
    exact bucket_spec ε (val A) hε ht.1 ht.2 _ hb

lemma ramsey_all {N : ℕ} (S : StoppingRule 0 N)
    (hsym : ∀ (I : Fin N) (v : Fin (I.val + 1) → ℝ) (π : Equiv.Perm (Fin (I.val + 1))),
      π (Fin.last I.val) = Fin.last I.val → S.r I ![] (v ∘ π) = S.r I ![] v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℕ, V.Infinite ∧ ∃ q : Fin N → ℝ, ∀ l, GoodAt S ε V l (q l) := by
  classical
  have key : ∀ m, m ≤ N → ∃ V : Set ℕ, V.Infinite ∧ ∃ q : Fin N → ℝ,
      ∀ l : Fin N, l.val < m → GoodAt S ε V l (q l) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨Set.univ, Set.infinite_univ, fun _ => 0, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨V, hV, q, hq⟩ := ih (by omega)
      obtain ⟨U, hUV, hU, ql, hql⟩ := ramsey_step S hsym ε hε V hV ⟨m, hm⟩
      refine ⟨U, hU, fun l => if l.val = m then ql else q l, fun l hl => ?_⟩
      by_cases hlm : l.val = m
      · simp only [hlm, if_true]
        have : l = ⟨m, hm⟩ := Fin.ext hlm
        subst this
        exact hql
      · simp only [hlm, if_false]
        exact GoodAt_mono S ε V U hUV l (q l) (hq l (by omega))
  obtain ⟨V, hV, q, hq⟩ := key N le_rfl
  exact ⟨V, hV, q, fun l => hq l l.isLt⟩


/-! ### Encoding a `(k,n)` rule as a `(0,k+n)` rule and decoding back -/

lemma r_congr {k n : ℕ} (R : StoppingRule k n) (I J : Fin n) (h : I = J) (s : Fin k → ℝ)
    (v : Fin (I.val + 1) → ℝ) (v' : Fin (J.val + 1) → ℝ)
    (hv : ∀ (a : Fin (I.val + 1)) (b : Fin (J.val + 1)), a.val = b.val → v a = v' b) :
    R.r I s v = R.r J s v' := by
  subst h
  congr 1
  funext a
  exact hv a a rfl

/-- Read the first `k` values as samples and never stop on them. -/
noncomputable def encR {k n : ℕ} (R : StoppingRule k n) : StoppingRule 0 (k + n) where
  r l _ v := if h : k ≤ l.val then
      R.r ⟨l.val - k, by have := l.isLt; omega⟩
        (fun a : Fin k => v ⟨a.val, by have := a.isLt; omega⟩)
        (fun b : Fin (l.val - k + 1) => v ⟨k + b.val, by have := b.isLt; omega⟩) else 0
  r_mem := by
    intro l s v
    split_ifs
    · exact R.r_mem _ _ _
    · exact ⟨le_refl 0, zero_le_one⟩

/-- Run a `(0,k+n)` rule on samples followed by values. -/
noncomputable def decR {k n : ℕ} (S : StoppingRule 0 (k + n)) : StoppingRule k n where
  r i s v := S.r (Fin.natAdd k i) ![] (@Fin.append k (i.val + 1) ℝ s v)
  r_mem i s v := S.r_mem _ _ _

lemma encR_lt {k n : ℕ} (R : StoppingRule k n) (j : Fin (k + n)) (hj : j.val < k)
    (s : Fin 0 → ℝ) (v : Fin (j.val + 1) → ℝ) : (encR R).r j s v = 0 := by
  simp only [encR]
  rw [dif_neg (by omega)]

lemma encR_natAdd {k n : ℕ} (R : StoppingRule k n) (s : Fin k → ℝ) (y : Fin n → ℝ) (j : Fin n) :
    (encR R).r (Fin.natAdd k j) ![]
        (Fin.append s y ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt)) =
      R.r j s (y ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) := by
  simp only [encR]
  rw [dif_pos (by simp)]
  have hs : (fun a : Fin k => (Fin.append s y ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt))
      ⟨a.val, by have := a.isLt; simp; omega⟩) = s := by
    funext a
    simp only [Function.comp_apply]
    have : (Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt)
        ⟨a.val, by have := a.isLt; simp; omega⟩ : Fin (k + n)) = Fin.castAdd n a := by
      ext; simp
    rw [this, Fin.append_left]
  rw [hs]
  apply r_congr R _ _ (by ext; simp)
  intro a b hab
  simp only [Function.comp_apply]
  have : (Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt)
      ⟨k + a.val, by have := a.isLt; simp; omega⟩ : Fin (k + n)) =
      Fin.natAdd k (Fin.castLE (Nat.succ_le_of_lt j.isLt) b) := by
    ext; simp [hab]
  rw [this, Fin.append_right]

lemma split_sum {k n : ℕ} (S : Finset ℝ) (f : (Fin (k + n) → ℝ) → ℝ) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin (k + n) => S), f x =
      ∑ s ∈ Fintype.piFinset (fun _ : Fin k => S), ∑ y ∈ Fintype.piFinset (fun _ : Fin n => S),
        f (Fin.append s y) := by
  rw [← Finset.sum_product' (f := fun s y => f (Fin.append s y))]
  symm
  apply Finset.sum_nbij' (fun p => Fin.append p.1 p.2)
    (fun x => (x ∘ Fin.castAdd n, x ∘ Fin.natAdd k))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro i
    induction i using Fin.addCases with
    | left a => rw [Fin.append_left]; exact hp.1 a
    | right b => rw [Fin.append_right]; exact hp.2 b
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hx ⊢
    exact ⟨fun a => hx _, fun b => hx _⟩
  · intro p _
    ext a
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  · intro x _
    exact Fin.append_castAdd_natAdd
  · intro p _; rfl

lemma iidWeight_append (F : FinDist) {k n : ℕ} (s : Fin k → ℝ) (y : Fin n → ℝ) :
    iidWeight F (Fin.append s y) = iidWeight F s * iidWeight F y := by
  unfold iidWeight
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

lemma expStop_zero'' {N : ℕ} (F : FinDist) (R : StoppingRule 0 N) :
    expStop F R = ∑ x ∈ Fintype.piFinset (fun _ : Fin N => F.supp),
      iidWeight F x * ∑ i, stopProb R ![] x i * x i := by
  unfold expStop
  have h0 : Fintype.piFinset (fun _ : Fin 0 => F.supp) = {![]} := by
    ext y
    simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [h0, Finset.sum_singleton]
  have h1 : iidWeight F (![] : Fin 0 → ℝ) = 1 := by simp [iidWeight]
  rw [h1]
  simp only [one_mul]

/-- Products over `Iio (natAdd k i)` reduce to products over `Iio i` when the factors at
the first `k` positions are `1`. -/
lemma prod_Iio_natAdd {k n : ℕ} (i : Fin n) (f : Fin (k + n) → ℝ) (g : Fin n → ℝ)
    (h1 : ∀ j : Fin (k + n), j.val < k → f j = 1)
    (h2 : ∀ j : Fin n, f (Fin.natAdd k j) = g j) :
    ∏ j ∈ Finset.Iio (Fin.natAdd k i), f j = ∏ j ∈ Finset.Iio i, g j := by
  classical
  have hsub : (Finset.Iio i).map (Fin.natAddEmb k) ⊆ Finset.Iio (Fin.natAdd k i) := by
    intro j hj
    simp only [Finset.mem_map, Finset.mem_Iio, Fin.natAddEmb_apply] at hj ⊢
    obtain ⟨b, hb, rfl⟩ := hj
    rw [Fin.lt_def] at hb ⊢
    simp; omega
  rw [← Finset.prod_subset hsub, Finset.prod_map]
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.natAddEmb_apply]
    exact h2 j
  · intro j hj hnot
    apply h1
    by_contra hc
    push Not at hc
    apply hnot
    simp only [Finset.mem_map, Finset.mem_Iio, Fin.natAddEmb_apply]
    refine ⟨⟨j.val - k, by have := j.isLt; omega⟩, ?_, ?_⟩
    · rw [Finset.mem_Iio, Fin.lt_def] at hj
      rw [Fin.lt_def]; simp at hj ⊢; omega
    · ext; simp; omega

lemma stopProb_encR_natAdd {k n : ℕ} (R : StoppingRule k n) (s : Fin k → ℝ) (y : Fin n → ℝ)
    (i : Fin n) :
    stopProb (encR R) ![] (Fin.append s y) (Fin.natAdd k i) = stopProb R s y i := by
  unfold stopProb
  rw [encR_natAdd]
  congr 1
  apply prod_Iio_natAdd
  · intro j hj
    rw [encR_lt R j hj]; ring
  · intro j
    rw [encR_natAdd]

lemma stopProb_encR_castAdd {k n : ℕ} (R : StoppingRule k n) (x : Fin (k + n) → ℝ)
    (a : Fin k) : stopProb (encR R) ![] x (Fin.castAdd n a) = 0 := by
  unfold stopProb
  rw [encR_lt R _ (by simp), mul_zero]

lemma stopProb_encR_castAdd' {k n : ℕ} (R : StoppingRule k n) (s : Fin 0 → ℝ)
    (x : Fin (k + n) → ℝ) (a : Fin k) : stopProb (encR R) s x (Fin.castAdd n a) = 0 := by
  unfold stopProb
  rw [encR_lt R _ (by simp), mul_zero]

lemma expStop_encR {k n : ℕ} (F : FinDist) (R : StoppingRule k n) :
    expStop F (encR R) = expStop F R := by
  rw [expStop_zero'', split_sum]
  unfold expStop
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [iidWeight_append, Fin.sum_univ_add]
  simp only [stopProb_encR_castAdd, zero_mul, Finset.sum_const_zero, zero_add,
    stopProb_encR_natAdd, Fin.append_right]

lemma decR_zero {k n : ℕ} (S : StoppingRule 0 (k + n))
    (hS : ∀ a : Fin k, NeverSelects S (Fin.castAdd n a)) (x : Fin (k + n) → ℝ)
    (hx : ∀ j, 0 ≤ x j) :
    ∀ j : Fin (k + n), j.val < k →
      S.r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) = 0 := by
  have key : ∀ m : ℕ, ∀ j : Fin (k + n), j.val = m → m < k →
      S.r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hjm hmk
      have hj : j.val < k := hjm ▸ hmk
      have h0 := hS ⟨j.val, hj⟩ ![] x (fun l => l.elim0) hx
      have e : (Fin.castAdd n ⟨j.val, hj⟩ : Fin (k + n)) = j := by ext; simp
      rw [e] at h0
      unfold stopProb at h0
      have hprod : ∏ l ∈ Finset.Iio j,
          (1 - S.r l ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt l.isLt))) = 1 := by
        apply Finset.prod_eq_one
        intro l hl
        have hl' : l.val < j.val := Fin.lt_def.mp (Finset.mem_Iio.mp hl)
        rw [ih l.val (by omega) l rfl (by omega), sub_zero]
      rw [hprod, one_mul] at h0
      exact h0
  intro j hj
  exact key j.val j rfl hj


lemma app_castLE {k n : ℕ} (s : Fin k → ℝ) (y : Fin n → ℝ) (j : Fin n) :
    (@Fin.append k (j.val + 1) ℝ s (y ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))) =
      (Fin.append s y) ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt) := by
  funext l
  induction l using Fin.addCases with
  | left a =>
    rw [Fin.append_left]
    simp only [Function.comp_apply]
    have : (Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt) (Fin.castAdd (j.val + 1) a) :
        Fin (k + n)) = Fin.castAdd n a := by ext; simp
    rw [this, Fin.append_left]
  | right b =>
    rw [Fin.append_right]
    simp only [Function.comp_apply]
    have : (Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt) (Fin.natAdd k b) :
        Fin (k + n)) = Fin.natAdd k (Fin.castLE (Nat.succ_le_of_lt j.isLt) b) := by ext; simp
    rw [this, Fin.append_right]

lemma stopProb_decR {k n : ℕ} (S : StoppingRule 0 (k + n))
    (hS : ∀ a : Fin k, NeverSelects S (Fin.castAdd n a)) (s : Fin k → ℝ) (y : Fin n → ℝ)
    (hs : ∀ j, 0 ≤ s j) (hy : ∀ j, 0 ≤ y j) (i : Fin n) :
    stopProb S ![] (Fin.append s y) (Fin.natAdd k i) = stopProb (decR S) s y i := by
  have hx : ∀ j, 0 ≤ Fin.append s y j := by
    intro j
    induction j using Fin.addCases with
    | left a => rw [Fin.append_left]; exact hs a
    | right b => rw [Fin.append_right]; exact hy b
  unfold stopProb
  have hr : ∀ j : Fin n, (decR S).r j s (y ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) =
      S.r (Fin.natAdd k j) ![]
        ((Fin.append s y) ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.natAdd k j).isLt)) := by
    intro j
    show S.r (Fin.natAdd k j) ![] _ = _
    rw [app_castLE]
  rw [hr i]
  congr 1
  apply prod_Iio_natAdd
  · intro j hj
    rw [decR_zero S hS _ hx j hj, sub_zero]
  · intro j
    rw [hr j]

lemma expStop_decR {k n : ℕ} (F : FinDist) (S : StoppingRule 0 (k + n))
    (hS : ∀ a : Fin k, NeverSelects S (Fin.castAdd n a)) :
    expStop F (decR S) = expStop F S := by
  rw [expStop_zero'' F S, split_sum]
  unfold expStop
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro y hy
  have hs' : ∀ j, 0 ≤ s j := fun j => F.supp_nonneg _ ((Fintype.mem_piFinset.mp hs) j)
  have hy' : ∀ j, 0 ≤ y j := fun j => F.supp_nonneg _ ((Fintype.mem_piFinset.mp hy) j)
  have hx : ∀ j, 0 ≤ Fin.append s y j := by
    intro j
    induction j using Fin.addCases with
    | left a => rw [Fin.append_left]; exact hs' a
    | right b => rw [Fin.append_right]; exact hy' b
  rw [iidWeight_append, Fin.sum_univ_add]
  have h0 : ∀ a : Fin k, stopProb S ![] (Fin.append s y) (Fin.castAdd n a) = 0 :=
    fun a => hS a ![] _ (fun j => j.elim0) hx
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add, Fin.append_right,
    stopProb_decR S hS s y hs' hy']

lemma decR_valueOblivious {k n : ℕ} (S : StoppingRule 0 (k + n)) (ε : ℝ) (V : Set ℕ)
    (q : Fin (k + n) → ℝ) (hq : ∀ l, GoodAt S ε V l (q l)) :
    ValueObliviousWith ε (decR S) V (fun i => q (Fin.natAdd k i)) := by
  intro i
  refine ⟨(hq (Fin.natAdd k i)).1, ?_⟩
  intro s v hsV hvV hinj hslt hvlt
  have hmem : ∀ j : Fin (k + (i.val + 1)), @Fin.append k (i.val + 1) ℕ s v j ∈ V := by
    intro j
    induction j using Fin.addCases with
    | left a => rw [Fin.append_left]; exact hsV a
    | right b => rw [Fin.append_right]; exact hvV b
  have hlast : (Fin.last (k + i.val) : Fin (k + (i.val + 1))) =
      Fin.natAdd k (Fin.last i.val) := by ext; simp
  have hrec : ∀ j : Fin (k + (i.val + 1)), j ≠ Fin.last (k + i.val) →
      @Fin.append k (i.val + 1) ℕ s v j < @Fin.append k (i.val + 1) ℕ s v (Fin.last (k + i.val)) := by
    intro j hj
    rw [hlast, Fin.append_right]
    induction j using Fin.addCases with
    | left a => rw [Fin.append_left]; exact hslt a
    | right b =>
      rw [Fin.append_right]
      apply hvlt
      intro hb; apply hj; rw [hb, hlast]
  have hg := (hq (Fin.natAdd k i)).2 (@Fin.append k (i.val + 1) ℕ s v) hmem hinj hrec
  have hfun : (fun j : Fin (k + (i.val + 1)) => ((@Fin.append k (i.val + 1) ℕ s v j : ℕ) : ℝ)) =
      @Fin.append k (i.val + 1) ℝ (fun j => (s j : ℝ)) (fun j => (v j : ℝ)) := by
    funext j
    induction j using Fin.addCases with
    | left a => simp [Fin.append_left]
    | right b => simp [Fin.append_right]
  show S.r (Fin.natAdd k i) ![] _ ∈ _
  rw [← hfun]
  exact hg

end UnknownProphet.NoSamples.Lemma1Aux

open UnknownProphet.NoSamples UnknownProphet.NoSamples.SymAux
  UnknownProphet.NoSamples.Lemma1Aux in
theorem solution (ε : ℝ) (hε : 0 < ε) (k n : ℕ) (α : ℝ)
    (h : ∃ R : StoppingRule k n, HasGuarantee R α) :
    ∃ R : StoppingRule k n,
      HasGuarantee R α ∧ ∃ V : Set ℕ, V.Infinite ∧ ValueOblivious ε R V := by
  obtain ⟨R, hR⟩ := h
  set S := symR (encR R)
  have hS : ∀ a : Fin k, NeverSelects S (Fin.castAdd n a) := by
    intro a
    apply symR_neverSelects
    intro s x _ _
    exact stopProb_encR_castAdd' R s x a
  have hsym : ∀ (I : Fin (k + n)) (v : Fin (I.val + 1) → ℝ) (π : Equiv.Perm (Fin (I.val + 1))),
      π (Fin.last I.val) = Fin.last I.val → S.r I ![] (v ∘ π) = S.r I ![] v :=
    fun I v π hπ => symR_symm (encR R) I v π hπ
  obtain ⟨V, hV, q, hq⟩ := ramsey_all S hsym ε hε
  refine ⟨decR S, ?_, V, hV, ⟨_, decR_valueOblivious S ε V q hq⟩⟩
  intro F
  rw [expStop_decR F S hS, expStop_symR, expStop_encR]
  exact hR F
