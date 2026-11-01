-- Prove2me | solution 1 for PayAsBid.SoftReserve.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:37:14.773042+00:00
-- url     : https://prove2.me/submissions/84581f3d-a7b7-4ff9-8cf4-c5cc1f6307b0

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model
import Theorems.Thm_PayAsBid_SoftReserve_lemma_1

namespace PayAsBid.SoftReserve.Aux

open PayAsBid.SoftReserve Matrix

variable {n : ℕ}

lemma Gamma_eq (P : Params n) (i j : Fin n) :
    P.Γ i j = -P.rc + (if i = j then P.ro + P.rc else 0) := by
  unfold Params.Γ; split_ifs <;> ring

lemma mu_pos (P : Params n) (hP : P.Standing) : 0 < P.ro - ((n : ℝ) - 1) * P.rc := by
  obtain ⟨hn, -, -, hpd, -⟩ := hP
  have hx : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have h := hpd.dotProduct_mulVec_pos hx
  have hval : star (fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (P.Γ *ᵥ fun _ => 1)
      = (n : ℝ) * (P.ro - ((n : ℝ) - 1) * P.rc) := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_one, one_mul, mul_one, Gamma_eq,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul]
    ring
  rw [hval] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact pos_of_mul_pos_right h hn'.le

/-- The explicit inverse. -/
noncomputable def Dmat (P : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((if i = j then 1 else 0) + P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc)

lemma Gamma_mul_Dmat (P : Params n) (hP : P.Standing) : P.Γ * Dmat P = 1 := by
  have hμ := mu_pos P hP
  have hK : 0 < P.ro + P.rc := by linarith [hP.2.1, hP.2.2.1]
  ext i j
  simp only [mul_apply, Dmat, Gamma_eq]
  have : ∀ l, (-P.rc + (if i = l then P.ro + P.rc else 0)) *
      (((if l = j then (1:ℝ) else 0) + P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc))
      = (-P.rc) * (if l = j then 1 else 0) / (P.ro + P.rc)
        + (-P.rc) * (P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc)
        + (if i = l then ((if l = j then 1 else 0) +
            P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) else 0) := by
    intro l
    split_ifs <;> field_simp <;> ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_div, zero_div, Finset.sum_ite_eq']
  rw [one_apply]
  have hμ' := hμ.ne'
  set μ := P.ro - ((n : ℝ) - 1) * P.rc with hμdef
  have hK' := hK.ne'
  split_ifs with h
  · subst h; field_simp; rw [hμdef]; ring
  · field_simp; rw [hμdef]; ring

lemma D_eq (P : Params n) (hP : P.Standing) : P.D = Dmat P := by
  unfold Params.D
  exact Matrix.inv_eq_right_inv (Gamma_mul_Dmat P hP)

/-- Key formula: on the simplex, consumer surplus is a constant minus a separable quadratic. -/
lemma CS_simplex (P : Params n) (hP : P.Standing) (x p : Fin n → ℝ) (hx : ∑ i, x i = 1) :
    CS P x p = (P.a / (P.ro - ((n : ℝ) - 1) * P.rc)
      - (1/2) * (P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc))
      - (1 / 2) * (∑ i, x i ^ 2) / (P.ro + P.rc) - ∑ i, p i * x i := by
  have hμ := (mu_pos P hP).ne'
  have hK : P.ro + P.rc ≠ 0 := by linarith [hP.2.1, hP.2.2.1]
  unfold CS Params.c
  rw [show P.Γ⁻¹ = P.D from rfl, D_eq P hP]
  simp only [dotProduct, mulVec, Dmat]
  have h1 : ∀ i, (∑ j, ((if i = j then (1:ℝ) else 0) + P.rc / (P.ro - ((n : ℝ) - 1) * P.rc))
      / (P.ro + P.rc) * P.a) * x i
      = P.a / (P.ro - ((n : ℝ) - 1) * P.rc) * x i := by
    intro i
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    set μ := P.ro - ((n : ℝ) - 1) * P.rc with hμdef
    field_simp
    rw [hμdef]; ring
  have h2 : ∀ i, x i * ∑ j, ((if i = j then (1:ℝ) else 0) +
      P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc) * x j
      = (x i ^ 2 + P.rc / (P.ro - ((n : ℝ) - 1) * P.rc) * x i * (∑ j, x j)) / (P.ro + P.rc) := by
    intro i
    have : ∀ j, ((if i = j then (1:ℝ) else 0) +
      P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc) * x j
      = (if i = j then x j else 0) / (P.ro + P.rc)
        + P.rc / (P.ro - ((n : ℝ) - 1) * P.rc) / (P.ro + P.rc) * x j := by
      intro j; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, ← Finset.sum_div]
    ring
  simp only [h1, h2, ← Finset.mul_sum, ← Finset.sum_div, hx]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hx]
  simp only [mul_comm (p _) (x _)]
  ring


/-- the separable objective -/
noncomputable def Fobj (P : Params n) (p x : Fin n → ℝ) : ℝ :=
  - ((1 / 2) * (∑ i, x i ^ 2) / (P.ro + P.rc)) - ∑ i, p i * x i

lemma CS_le_iff (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (p x y : Fin n → ℝ)
    (hx : Admissible Q x) (hy : Admissible Q y) :
    CS P y p ≤ CS P x p ↔ Fobj P p y ≤ Fobj P p x := by
  rw [CS_simplex P hP x p hx.1, CS_simplex P hP y p hy.1]
  unfold Fobj
  constructor <;> intro h <;> linarith

lemma admissible_nonempty (Q : Finset (Fin n)) (hQ : Q.Nonempty) : ∃ x, Admissible Q x := by
  obtain ⟨j, hj⟩ := hQ
  refine ⟨fun i => if i = j then 1 else 0, ?_, ?_, ?_⟩
  · simp
  · intro i; show (0:ℝ) ≤ if i = j then 1 else 0
    split_ifs <;> norm_num
  · intro i hi; have : i ≠ j := fun h => hi (h ▸ hj)
    simp [this]

lemma admissible_le_one (Q : Finset (Fin n)) (x : Fin n → ℝ) (hx : Admissible Q x) (i : Fin n) :
    x i ≤ 1 := by
  rw [← hx.1]
  exact Finset.single_le_sum (fun j _ => hx.2.1 j) (Finset.mem_univ i)

lemma isCompact_admissible (Q : Finset (Fin n)) : IsCompact {x : Fin n → ℝ | Admissible Q x} := by
  have hsub : {x : Fin n → ℝ | Admissible Q x} ⊆ Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) := by
    intro x hx i _
    exact ⟨hx.2.1 i, admissible_le_one Q x hx i⟩
  refine (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset ?_ hsub
  have h1 : IsClosed {x : Fin n → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ => (continuous_apply i : Continuous fun x : Fin n → ℝ => x i))) continuous_const
  have h2 : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i : Continuous fun x : Fin n → ℝ => x i)
  have h3 : IsClosed {x : Fin n → ℝ | ∀ i, i ∉ Q → x i = 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ Q
    · simp [hi]
    · simp only [hi, not_false_eq_true, Set.iInter_true]
      exact isClosed_eq (continuous_apply i : Continuous fun x : Fin n → ℝ => x i) continuous_const
  have : {x : Fin n → ℝ | Admissible Q x} =
      {x | ∑ i, x i = 1} ∩ {x | ∀ i, 0 ≤ x i} ∩ {x | ∀ i, i ∉ Q → x i = 0} := by
    ext x; simp [Admissible, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

lemma exists_demand (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (p : Fin n → ℝ) : ∃ x, IsDemand P Q p x := by
  obtain ⟨x0, hx0⟩ := admissible_nonempty Q hQ
  have hcont : Continuous (Fobj P p) := by unfold Fobj; fun_prop
  obtain ⟨x, hx, hmax⟩ := (isCompact_admissible Q).exists_isMaxOn ⟨x0, hx0⟩ hcont.continuousOn
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [CS_le_iff P hP Q p x y hx hy]
  exact hmax hy

lemma demand_spec (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (p : Fin n → ℝ) : IsDemand P Q p (demand P Q p) := by
  have h := exists_demand P hP Q hQ p
  unfold demand
  rw [dif_pos h]
  exact h.choose_spec

lemma demand_nonneg (P : Params n) (Q : Finset (Fin n)) (p : Fin n → ℝ) (i : Fin n) :
    0 ≤ demand P Q p i := by
  unfold demand
  split_ifs with h
  · exact h.choose_spec.1.2.1 i
  · simp

lemma demand_zero_of_not_mem (P : Params n) (Q : Finset (Fin n)) (p : Fin n → ℝ) (i : Fin n)
    (hi : i ∉ Q) : demand P Q p i = 0 := by
  unfold demand
  split_ifs with h
  · exact h.choose_spec.1.2.2 i hi
  · simp

lemma demand_sum (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (p : Fin n → ℝ) : ∑ i, demand P Q p i = 1 :=
  (demand_spec P hP Q hQ p).1.1

/-- First-order condition: mass sits only on minimal marginal cost coordinates. -/
lemma foc (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (p x : Fin n → ℝ)
    (hx : IsDemand P Q p x) (j l : Fin n) (hl : l ∈ Q) (hj : 0 < x j) :
    x j / (P.ro + P.rc) + p j ≤ x l / (P.ro + P.rc) + p l := by
  have hK : 0 < P.ro + P.rc := by linarith [hP.2.1, hP.2.2.1]
  by_cases hlj : l = j
  · subst hlj; exact le_rfl
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ x j →
      0 ≤ (x l - x j) / (P.ro + P.rc) + ε / (P.ro + P.rc) + (p l - p j) := by
    intro ε hε hεj
    set y : Fin n → ℝ := fun i => x i + ε * (if i = l then 1 else 0) - ε * (if i = j then 1 else 0)
      with hydef
    have hy : Admissible Q y := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [hydef, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, hx.1.1]
        ring
      · intro i
        simp only [hydef]
        have := hx.1.2.1 i
        by_cases h1 : i = l
        · subst h1; simp [hlj]; linarith
        · by_cases h2 : i = j
          · subst h2; simp [h1]; linarith
          · simp [h1, h2]; linarith
      · intro i hi
        have h1 : i ≠ l := fun h => hi (h ▸ hl)
        have h2 : i ≠ j := by
          intro h; subst h; have := hx.1.2.2 i hi; linarith
        simp [hydef, h1, h2, hx.1.2.2 i hi]
    have hle := (CS_le_iff P hP Q p x y hx.1 hy).1 (hx.2 y hy)
    have hsq : ∀ i, y i ^ 2 = x i ^ 2 + (2 * ε * x l + ε ^ 2) * (if i = l then 1 else 0)
        + (-2 * ε * x j + ε ^ 2) * (if i = j then 1 else 0) := by
      intro i
      simp only [hydef]
      by_cases h1 : i = l
      · subst h1; simp [hlj]; ring
      · by_cases h2 : i = j
        · subst h2; simp [h1]; ring
        · simp [h1, h2]
    have hpy : ∀ i, p i * y i = p i * x i + (ε * p l) * (if i = l then 1 else 0)
        + (-ε * p j) * (if i = j then 1 else 0) := by
      intro i
      simp only [hydef]
      by_cases h1 : i = l
      · subst h1; simp [hlj]; ring
      · by_cases h2 : i = j
        · subst h2; simp [h1]; ring
        · simp [h1, h2]
    unfold Fobj at hle
    simp only [hsq, hpy, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_one] at hle
    generalize ∑ i, x i ^ 2 = S at hle
    generalize ∑ i, p i * x i = T at hle
    have : 0 ≤ ((x l - x j) / (P.ro + P.rc) + ε / (P.ro + P.rc) + (p l - p j)) * ε := by
      have e : ((x l - x j) / (P.ro + P.rc) + ε / (P.ro + P.rc) + (p l - p j)) * ε
        = (-((1 / 2) * S / (P.ro + P.rc)) - T) - (-((1 / 2) * (S + (2 * ε * x l + ε ^ 2)
            + (-2 * ε * x j + ε ^ 2)) / (P.ro + P.rc)) - (T + ε * p l + -ε * p j)) := by
        field_simp; ring
      rw [e]; linarith
    exact nonneg_of_mul_nonneg_left this hε
  by_contra hcon
  push Not at hcon
  set d := (x l - x j) / (P.ro + P.rc) + (p l - p j) with hd
  have hdneg : d < 0 := by
    have : x l / (P.ro + P.rc) - x j / (P.ro + P.rc) = (x l - x j) / (P.ro + P.rc) := by ring
    linarith
  set ε := min (x j) (-d * (P.ro + P.rc) / 2) with hε
  have hε0 : 0 < ε := lt_min hj (by nlinarith)
  have h := key ε hε0 (min_le_left _ _)
  have h2 : ε / (P.ro + P.rc) ≤ -d / 2 := by
    rw [div_le_iff₀ hK]; have := min_le_right (x j) (-d * (P.ro + P.rc) / 2); linarith
  linarith

lemma demand_antitone (P : Params n) (hP : P.Standing) (Q Q' : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ Q) (hQQ' : Q ⊆ Q') (p : Fin n → ℝ) :
    demand P Q' p i ≤ demand P Q p i := by
  have hK : 0 < P.ro + P.rc := by linarith [hP.2.1, hP.2.2.1]
  have hQ : Q.Nonempty := ⟨i, hi⟩
  have hQ' : Q'.Nonempty := ⟨i, hQQ' hi⟩
  set x := demand P Q' p
  set y := demand P Q p
  have hx := demand_spec P hP Q' hQ' p
  have hy := demand_spec P hP Q hQ p
  by_contra hcon
  push Not at hcon
  have hxi : 0 < x i := lt_of_le_of_lt (demand_nonneg P Q p i) hcon
  have hle : ∀ l ∈ Q, y l ≤ x l := by
    intro l hl
    by_contra h
    push Not at h
    have hyl : 0 < y l := lt_of_le_of_lt (demand_nonneg P Q' p l) h
    have f1 := foc P hP Q p y hy l i hi hyl
    have f2 := foc P hP Q' p x hx i l (hQQ' hl) hxi
    have : y i / (P.ro + P.rc) < x i / (P.ro + P.rc) := div_lt_div_of_pos_right hcon hK
    have : y l / (P.ro + P.rc) < x l / (P.ro + P.rc) := by linarith
    have : y l < x l := (div_lt_div_iff_of_pos_right hK).1 this
    linarith
  have hsy : ∑ l ∈ Q, y l = 1 := by
    rw [← hy.1.1]
    exact Finset.sum_subset (Finset.subset_univ Q) (fun l _ hl => hy.1.2.2 l hl)
  have hsx : ∑ l ∈ Q, x l ≤ 1 := by
    rw [← hx.1.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
      (fun l _ _ => hx.1.2.1 l)
  have : ∑ l ∈ Q, y l < ∑ l ∈ Q, x l := Finset.sum_lt_sum hle ⟨i, hi, hcon⟩
  linarith

end PayAsBid.SoftReserve.Aux

namespace PayAsBid.SoftReserve.Aux

open PayAsBid.SoftReserve

variable {n : ℕ}

lemma bool_le_false {a : Bool} (h : a ≤ false) : a = false := by
  revert h; cases a <;> decide

lemma bool_true_le {a : Bool} (h : true ≤ a) : a = true := by
  revert h; cases a <;> decide

lemma decide_le_decide' {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    decide p ≤ decide q := by
  by_cases hp : p
  · simp [hp, h hp]
  · simp [hp]

lemma weight_pos (P : Params n) (hP : P.Standing) (θ : Fin n → Bool) : 0 < weight P θ := by
  obtain ⟨-, -, -, -, -, -, hf0, hf1⟩ := hP
  unfold weight
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact hf0
  · linarith

noncomputable def U (P : Params n) (q : AssortFn n) (bL bH : ℝ) (i : Fin n) (b' : ℝ) : ℝ :=
  ∑ θ : Fin n → Bool, weight P θ * alloc P q (Function.update (price bL bH θ) i b') i

lemma utility_eq (P : Params n) (q : AssortFn n) (bL bH : ℝ) (i : Fin n) (t : Bool) (b' : ℝ) :
    utility P q bL bH i t b' = (b' - cost P t) * U P q bL bH i b' := by
  unfold utility U
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun θ _ => by ring)

lemma alloc_nonneg (P : Params n) (q : AssortFn n) (b : Fin n → ℝ) (i : Fin n) :
    0 ≤ alloc P q b i := demand_nonneg P _ b i

lemma U_nonneg (P : Params n) (hP : P.Standing) (q : AssortFn n) (bL bH : ℝ) (i : Fin n)
    (b' : ℝ) : 0 ≤ U P q bL bH i b' :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (weight_pos P hP θ).le (alloc_nonneg P q _ i)

lemma update_price (bL bH : ℝ) (θ : Fin n → Bool) (i : Fin n) (t : Bool) :
    Function.update (price bL bH θ) i (if t then bL else bH)
      = price bL bH (Function.update θ i t) := by
  ext j
  by_cases h : j = i
  · subst h; simp [price]
  · simp [price, Function.update_of_ne h]

lemma price_nonneg {bL bH : ℝ} (hbL : 0 ≤ bL) (hbH : 0 ≤ bH) (θ : Fin n → Bool) :
    Nonneg (price bL bH θ) := fun j => by
  unfold price; split_ifs <;> assumption

/-- Lemma 3 (already from feasibility). -/
theorem lemma3_of_feasible (P : Params n) (hP : P.Standing) (q : AssortFn n) (r bL bH : ℝ)
    (hF : Feasible8 P q r bL bH) : bL ≤ bH := by
  obtain ⟨hBL, hBH, hIRL, hIRH, -, -, -, -, hne⟩ := hF
  have hθL := hP.2.2.2.2.1
  have hθLH := hP.2.2.2.2.2.1
  by_contra hlt
  push Not at hlt
  have hbH0 : 0 ≤ bH := by linarith
  have hbL0 : 0 ≤ bL := by linarith
  have hU : ∀ i, U P q bL bH i bL = 0 ∧ U P q bL bH i bH = 0 := by
    intro i
    have h1 := hBL i bH hbH0
    have h2 := hBH i bL hbL0
    rw [utility_eq, utility_eq] at h1 h2
    simp only [cost, if_true, Bool.false_eq_true, if_false] at h1 h2
    have u1 := U_nonneg P hP q bL bH i bL
    have u2 := U_nonneg P hP q bL bH i bH
    set UL := U P q bL bH i bL
    set UH := U P q bL bH i bH
    have hs : (P.θH - P.θL) * UH ≤ (P.θH - P.θL) * UL := by linarith
    have hle : UH ≤ UL := le_of_mul_le_mul_left hs (by linarith)
    have h3 : (bH - P.θH) * UH ≤ (bH - P.θH) * UL := mul_le_mul_of_nonneg_left hle (by linarith)
    have h4 : (bL - bH) * UL ≤ 0 := by linarith
    have h5 : UL ≤ 0 := by
      by_contra h; push Not at h
      have : 0 < (bL - bH) * UL := mul_pos (by linarith) h
      linarith
    exact ⟨le_antisymm h5 u1, le_antisymm (hle.trans h5) u2⟩
  have hz : ∀ i θ, alloc P q (price bL bH θ) i = 0 := by
    intro i θ
    have hterm : ∀ b', U P q bL bH i b' = 0 → ∀ θ' : Fin n → Bool,
        weight P θ' * alloc P q (Function.update (price bL bH θ') i b') i = 0 := by
      intro b' hb θ'
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => mul_nonneg (weight_pos P hP θ).le
        (alloc_nonneg P q _ i))).1 hb θ' (Finset.mem_univ _)
    have hupd : Function.update (price bL bH θ) i (if θ i then bL else bH) = price bL bH θ := by
      rw [update_price, Function.update_eq_self]
    have key := hterm (if θ i then bL else bH) (by cases θ i <;> simp [(hU i).1, (hU i).2]) θ
    rw [hupd] at key
    exact (mul_eq_zero.1 key).resolve_left (weight_pos P hP θ).ne'
  have hsum := demand_sum P hP _ (hne (fun _ => true)) (price bL bH (fun _ => true))
  have : ∑ i, alloc P q (price bL bH (fun _ => true)) i = 0 :=
    Finset.sum_eq_zero fun i _ => hz i _
  unfold alloc at this
  linarith

lemma bH_le_r (P : Params n) (q : AssortFn n) (r bL bH : ℝ) (hF : Feasible8 P q r bL bH)
    (hbL : 0 ≤ bL) (hbH : 0 ≤ bH) : bH ≤ r := by
  obtain ⟨-, -, -, -, -, hRP, -, -, hne⟩ := hF
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := hne (fun _ => false)
  simp only [assortSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have := hRP (price bL bH (fun _ => false)) (price_nonneg hbL hbH _) j (by simpa [price] using h)
  rw [this] at hj
  exact Bool.false_ne_true hj

/-- number of low types -/
def cnt (θ : Fin n → Bool) : ℕ := (Finset.univ.filter fun j => θ j = true).card

lemma exists_perm (θ θ' : Fin n → Bool) (h : cnt θ = cnt θ') :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, θ (σ j) = θ' j := by
  have e1 : Fintype.card {x // θ' x = true} = Fintype.card {x // θ x = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact h.symm
  have e2 : Fintype.card {x // ¬ θ' x = true} = Fintype.card {x // ¬ θ x = true} :=
    Fintype.card_compl_eq_card_compl _ _ e1
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq e1) (Fintype.equivOfCardEq e2), ?_⟩
  intro j
  by_cases hj : θ' j = true
  · have := ((Fintype.equivOfCardEq e1) ⟨j, hj⟩).2
    simp only [Equiv.subtypeCongr, Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x => θ' x = true) hj, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl, this, hj]
  · have := ((Fintype.equivOfCardEq e2) ⟨j, hj⟩).2
    simp only [Equiv.subtypeCongr, Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun x => θ' x = true) hj, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    simp only [Bool.not_eq_true] at this hj
    rw [this, hj]

lemma highs_same (q : AssortFn n) (hq : Anonymous q) (bL bH : ℝ) (θ : Fin n → Bool)
    (hb : Nonneg (price bL bH θ)) (j j' : Fin n) (hj : θ j = false) (hj' : θ j' = false) :
    q (price bL bH θ) j = q (price bL bH θ) j' := by
  have hσ : price bL bH θ ∘ Equiv.swap j j' = price bL bH θ := by
    ext l
    simp only [Function.comp_apply, price]
    rcases eq_or_ne l j with h1 | h1
    · subst h1; simp [hj, hj']
    · rcases eq_or_ne l j' with h2 | h2
      · subst h2; simp [hj, hj']
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have := congrFun (hq (Equiv.swap j j') _ hb) j
  rw [hσ] at this
  rw [this]; simp

lemma highs_transfer (q : AssortFn n) (hq : Anonymous q) (bL bH : ℝ) (hbL : 0 ≤ bL)
    (hbH : 0 ≤ bH) (θ θ' : Fin n → Bool) (h : cnt θ = cnt θ') (j j' : Fin n)
    (hj : θ j = false) (hj' : θ' j' = false) :
    q (price bL bH θ') j' = q (price bL bH θ) j := by
  obtain ⟨σ, hσ⟩ := exists_perm θ θ' h
  have hp : price bL bH θ' = price bL bH θ ∘ σ := by
    ext l; simp [price, hσ]
  have := congrFun (hq σ _ (price_nonneg hbL hbH θ)) j'
  rw [← hp] at this
  rw [this, Function.comp_apply]
  exact highs_same q hq bL bH θ (price_nonneg hbL hbH θ) _ _ (by rw [hσ, hj']) hj

def Eprop (q : AssortFn n) (bL bH : ℝ) (m : ℕ) : Prop :=
  ∃ θ : Fin n → Bool, cnt θ = m ∧ ∃ j, θ j = false ∧ q (price bL bH θ) j = false

lemma card_false (θ : Fin n → Bool) :
    cnt θ + (Finset.univ.filter fun j => θ j = false).card = n := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun j => θ j = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  exact this

lemma E_step (q : AssortFn n) (hmono : IsMonotone q) (bL bH : ℝ) (hbL : 0 ≤ bL)
    (hlt : bL < bH) (m : ℕ) (hm : m + 1 < n) (hE : Eprop q bL bH m) : Eprop q bL bH (m + 1) := by
  obtain ⟨θ, hc, j, hj, hqj⟩ := hE
  have hcard := card_false θ
  have h1 : 1 < (Finset.univ.filter fun j => θ j = false).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1
  obtain ⟨j', hj'F, hj'j⟩ : ∃ j' ∈ (Finset.univ.filter fun j => θ j = false), j' ≠ j := by
    by_cases haj : a = j
    · exact ⟨b, hb, fun h => hab (haj.trans h.symm)⟩
    · exact ⟨a, ha, haj⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'F
  refine ⟨Function.update θ j' true, ?_, j, ?_, ?_⟩
  · unfold cnt
    have : (Finset.univ.filter fun l => Function.update θ j' true l = true)
        = insert j' (Finset.univ.filter fun l => θ l = true) := by
      ext l
      by_cases hl : l = j'
      · subst hl; simp
      · simp [Function.update_of_ne hl, hl]
    rw [this, Finset.card_insert_of_notMem (by simp [hj'F])]
    unfold cnt at hc; omega
  · rw [Function.update_of_ne hj'j.symm]; exact hj
  · have hb0 : Nonneg (price bL bH θ) := price_nonneg hbL (by linarith) θ
    have hlt' : bL < price bL bH θ j' := by simp [price, hj'F]; exact hlt
    have := (hmono _ hb0 j' bL hbL hlt').2 j hj'j.symm
    have hu := update_price bL bH θ j' true
    simp only [if_true] at hu
    rw [hu, hqj] at this
    exact bool_le_false this

lemma E_mono (q : AssortFn n) (hmono : IsMonotone q) (bL bH : ℝ) (hbL : 0 ≤ bL)
    (hlt : bL < bH) (a m : ℕ) (ham : a ≤ m) (hm : m < n) (hE : Eprop q bL bH a) :
    Eprop q bL bH m := by
  induction m, ham using Nat.le_induction with
  | base => exact hE
  | succ m hm' ih => exact E_step q hmono bL bH hbL hlt m hm (ih (by omega))

lemma cnt_lt_of_false (θ : Fin n → Bool) (j : Fin n) (hj : θ j = false) : cnt θ < n := by
  have := card_false θ
  have : 0 < (Finset.univ.filter fun l => θ l = false).card :=
    Finset.card_pos.2 ⟨j, by simp [hj]⟩
  omega

lemma all_false_of_cnt (θ : Fin n → Bool) (h : cnt θ = 0) : ∀ l, θ l = false := by
  intro l
  unfold cnt at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  simpa using h (Finset.mem_univ l)

lemma kSR_price (k : ℕ) (bL bH : ℝ) (hlt : bL < bH) (θ : Fin n → Bool) (j : Fin n) :
    kSR k bL bH (price bL bH θ) j = (θ j || decide (cnt θ < k)) := by
  have hf : (Finset.univ.filter fun l => price bL bH θ l ≤ bL)
      = Finset.univ.filter fun l => θ l = true := by
    exact Finset.filter_congr (fun l _ => by cases h : θ l <;> simp [price, h, not_le.2 hlt])
  unfold kSR
  rw [hf]
  cases h : θ j
  · simp [price, h, hlt, cnt]
    rfl
  · simp [price, h, hlt.le]

theorem matching (P : Params n) (hP : P.Standing) (q : AssortFn n) (r bL bH : ℝ)
    (hF : Feasible8 P q r bL bH) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ ∀ θ, q (price bL bH θ) = kSR k bL bH (price bL bH θ) := by
  have hle := lemma3_of_feasible P hP q r bL bH hF
  have hn := hP.1
  have hbL : 0 ≤ bL := by linarith [hF.2.2.1, hP.2.2.2.2.1]
  have hbH : 0 ≤ bH := by linarith
  have hr := bH_le_r P q r bL bH hF hbL hbH
  obtain ⟨-, -, -, -, ⟨hanon, hmono⟩, hRP, -, hTD, -⟩ := hF
  have L1 := lemma_1 hn q r ⟨hanon, hmono⟩ hRP hTD
  rcases hle.lt_or_eq with hlt | heq
  swap
  · -- bL = bH
    subst heq
    refine ⟨n, hn, le_rfl, fun θ => ?_⟩
    have hp : price bL bL θ = fun _ => bL := by ext l; simp [price]
    rw [hp, L1.1 bL hbL hr]
    ext j; simp [kSR]
  -- bL < bH
  have hlow : ∀ θ j, θ j = true → q (price bL bH θ) j = true := by
    intro θ j hj
    refine L1.2 _ (price_nonneg hbL hbH θ) j (by simp [price, hj]; linarith) ?_
    intro l _
    simp only [price, hj, if_true]
    split_ifs <;> linarith
  have hzero : ∀ θ : Fin n → Bool, cnt θ = 0 → ∀ j, q (price bL bH θ) j = true := by
    intro θ h0 j
    have hp : price bL bH θ = fun _ => bH := by
      ext l; simp [price, all_false_of_cnt θ h0 l]
    rw [hp, L1.1 bH hbH hr]
  by_cases hex : ∃ m, 1 ≤ m ∧ m < n ∧ Eprop q bL bH m
  · classical
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1.le, fun θ => ?_⟩
    ext j
    rw [kSR_price _ bL bH hlt θ j]
    cases hj : θ j
    · simp only [Bool.false_or]
      rcases Nat.eq_zero_or_pos (cnt θ) with h0 | hpos
      · rw [hzero θ h0 j, h0]; simp [(Nat.find_spec hex).1]
      · have hcn := cnt_lt_of_false θ j hj
        cases hv : q (price bL bH θ) j
        · have : Nat.find hex ≤ cnt θ := Nat.find_min' hex ⟨hpos, hcn, θ, rfl, j, hj, hv⟩
          rw [eq_comm, decide_eq_false_iff_not]; omega
        · rw [eq_comm, decide_eq_true_iff]
          by_contra hcon
          push Not at hcon
          have hk := Nat.find_spec hex
          obtain ⟨θ', hc', j', hj', hv'⟩ := E_mono q hmono bL bH hbL hlt _ _ (by
            simpa using hcon) hcn hk.2.2
          have := highs_transfer q hanon bL bH hbL hbH θ' θ hc' j' j hj' hj
          rw [this, hv'] at hv
          exact Bool.false_ne_true hv
    · simp [hlow θ j hj]
  · refine ⟨n, hn, le_rfl, fun θ => ?_⟩
    ext j
    rw [kSR_price _ bL bH hlt θ j]
    cases hj : θ j
    · simp only [Bool.false_or]
      have hcn := cnt_lt_of_false θ j hj
      rcases Nat.eq_zero_or_pos (cnt θ) with h0 | hpos
      · rw [hzero θ h0 j]; simp [hcn]
      · cases hv : q (price bL bH θ) j
        · exact absurd ⟨cnt θ, hpos, hcn, θ, rfl, j, hj, hv⟩ hex
        · simp [hcn]
    · simp [hlow θ j hj]

end PayAsBid.SoftReserve.Aux

namespace PayAsBid.SoftReserve.Aux

open PayAsBid.SoftReserve

variable {n : ℕ}

lemma kSR_anon (k : ℕ) (s r : ℝ) : Anonymous (kSR (n := n) k s r) := by
  intro σ b _
  ext j
  have hc : (Finset.univ.filter fun l => b (σ l) ≤ s).card
      = (Finset.univ.filter fun l => b l ≤ s).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (σ.subtypeEquiv (fun a => Iff.rfl))
  simp only [kSR, Function.comp_apply, hc]

lemma kSR_mono (k : ℕ) (s r : ℝ) : IsMonotone (kSR (n := n) k s r) := by
  intro b _ i b' _ hlt
  have hsub : (Finset.univ.filter fun l => b l ≤ s) ⊆
      (Finset.univ.filter fun l => Function.update b i b' l ≤ s) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    by_cases h : l = i
    · subst h; simp only [Function.update_self]; linarith
    · rw [Function.update_of_ne h]; exact hl
  have hcc := Finset.card_le_card hsub
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [kSR, Function.update_self]
    apply decide_le_decide'
    intro hA hB
    rcases hB with h1 | ⟨h1, h2, h3⟩
    · exact hA (Or.inl (by linarith))
    · have hceq : (Finset.univ.filter fun l => Function.update b i b' l ≤ s)
          = (Finset.univ.filter fun l => b l ≤ s) := by
        refine Finset.filter_congr (fun l _ => ?_)
        by_cases h : l = i
        · subst h; simp only [Function.update_self]
          constructor <;> intro h' <;> linarith
        · rw [Function.update_of_ne h]
      rw [hceq] at h3
      by_cases hbr : r < b i
      · exact hA (Or.inl hbr)
      · push Not at hbr
        exact hA (Or.inr ⟨by linarith, hbr, h3⟩)
  · simp only [kSR, Function.update_of_ne hj]
    apply decide_le_decide'
    intro hA hB
    apply hA
    rcases hB with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, le_trans h3 hcc⟩

lemma kSR_RP1 (k : ℕ) (s r : ℝ) : ReserveRP1 (kSR (n := n) k s r) r := by
  intro b _ i h
  simp [kSR, h]

lemma kSR_TD (k : ℕ) (s r : ℝ) (hk : 1 ≤ k) (hsr : s ≤ r) :
    TotalDemandOne (kSR (n := n) k s r) r := by
  intro b _ ⟨i, hi⟩
  by_cases hs : ∃ j, b j ≤ s
  · obtain ⟨j, hj⟩ := hs
    refine ⟨j, ?_⟩
    simp only [kSR, decide_eq_true_eq]
    intro h
    rcases h with h | ⟨h1, -⟩ <;> linarith
  · have h0 : (Finset.univ.filter fun l => b l ≤ s).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro l _
      push Not at hs
      exact not_le.2 (hs l)
    refine ⟨i, ?_⟩
    simp only [kSR, decide_eq_true_eq, h0]
    intro h
    rcases h with h | ⟨-, -, h⟩
    · linarith
    · omega

lemma kSR_update_congr (k : ℕ) (s r : ℝ) (b : Fin n → ℝ) (i : Fin n) (x y : ℝ)
    (h1 : x ≤ s ↔ y ≤ s) (h2 : r < x ↔ r < y) :
    kSR k s r (Function.update b i x) = kSR k s r (Function.update b i y) := by
  have hc : (Finset.univ.filter fun l => Function.update b i x l ≤ s)
      = (Finset.univ.filter fun l => Function.update b i y l ≤ s) := by
    refine Finset.filter_congr (fun l _ => ?_)
    by_cases h : l = i
    · subst h; simp only [Function.update_self]; exact h1
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  have h3 : s < x ↔ s < y := by rw [← not_le, ← not_le, h1]
  have h4 : x ≤ r ↔ y ≤ r := by rw [← not_lt, ← not_lt, h2]
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [kSR, Function.update_self, hc, h2, h3, h4]
  · simp only [kSR, Function.update_of_ne hj, hc]

lemma alloc_kSR_le (P : Params n) (hP : P.Standing) (q : AssortFn n) (hmono : IsMonotone q)
    (k : ℕ) (bL bH : ℝ) (hbL0 : 0 ≤ bL) (hle : bL ≤ bH)
    (hmatch : ∀ θ, q (price bL bH θ) = kSR k bL bH (price bL bH θ))
    (θ : Fin n → Bool) (i : Fin n) (b' : ℝ) (hb'0 : 0 ≤ b') (hb' : b' ≤ bH) :
    alloc P (kSR k bL bH) (Function.update (price bL bH θ) i b') i
      ≤ alloc P q (Function.update (price bL bH θ) i b') i := by
  obtain ⟨t, hct, hkeq⟩ : ∃ t : Bool, b' ≤ (if t then bL else bH) ∧
      kSR k bL bH (Function.update (price bL bH θ) i b')
        = kSR k bL bH (Function.update (price bL bH θ) i (if t then bL else bH)) := by
    by_cases hbl : b' ≤ bL
    · refine ⟨true, by simpa using hbl, ?_⟩
      simp only [if_true]
      exact kSR_update_congr k bL bH _ i b' bL ⟨fun _ => le_rfl, fun _ => hbl⟩
        ⟨fun h => by linarith, fun h => by linarith⟩
    · push Not at hbl
      refine ⟨false, by simpa using hb', ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact kSR_update_congr k bL bH _ i b' bH ⟨fun h => by linarith, fun h => by linarith⟩
        ⟨fun h => by linarith, fun h => by linarith⟩
  set c := if t then bL else bH with hc
  set b0 := Function.update (price bL bH θ) i c with hb0
  have hb0eq : b0 = price bL bH (Function.update θ i t) := update_price bL bH θ i t
  have hq0 : q b0 = kSR k bL bH b0 := by rw [hb0eq]; exact hmatch _
  have hbb0 : Function.update (price bL bH θ) i b' = Function.update b0 i b' := by
    rw [hb0, Function.update_idem]
  have hrel : q b0 i ≤ q (Function.update (price bL bH θ) i b') i ∧
      ∀ j, j ≠ i → q (Function.update (price bL bH θ) i b') j ≤ q b0 j := by
    rcases hct.lt_or_eq with hlt | heq
    · have hb0n : Nonneg b0 := by
        rw [hb0eq]; exact price_nonneg hbL0 (by linarith) _
      have hlt' : b' < b0 i := by rw [hb0, Function.update_self]; exact hlt
      rw [hbb0]
      exact hmono b0 hb0n i b' hb'0 hlt'
    · have : Function.update (price bL bH θ) i b' = b0 := by rw [hb0, heq]
      rw [this]; exact ⟨le_rfl, fun j _ => le_rfl⟩
  by_cases hki : kSR k bL bH (Function.update (price bL bH θ) i b') i = true
  · unfold alloc
    apply demand_antitone P hP
    · have h0 : q b0 i = true := by rw [hq0, ← hkeq]; exact hki
      have := hrel.1
      rw [h0] at this
      simp only [assortSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact bool_true_le this
    · intro j hj
      simp only [assortSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_cases hji : j = i
      · subst hji; exact hki
      · have := hrel.2 j hji
        rw [hj] at this
        have h1 := bool_true_le this
        rw [hq0, ← hkeq] at h1
        exact h1
  · have : i ∉ assortSet (kSR k bL bH) (Function.update (price bL bH θ) i b') := by
      simp [assortSet, hki]
    unfold alloc
    rw [demand_zero_of_not_mem P _ _ i this]
    exact demand_nonneg P _ _ i

lemma kSR_BN (P : Params n) (hP : P.Standing) (q : AssortFn n) (r bL bH : ℝ)
    (hF : Feasible8 P q r bL bH) (k : ℕ) (hle : bL ≤ bH)
    (hmatch : ∀ θ, q (price bL bH θ) = kSR k bL bH (price bL bH θ))
    (t : Bool) (i : Fin n) (b' : ℝ) (hb' : 0 ≤ b') :
    utility P (kSR k bL bH) bL bH i t b'
      ≤ utility P (kSR k bL bH) bL bH i t (if t then bL else bH) := by
  have hθL := hP.2.2.2.2.1
  have hθLH := hP.2.2.2.2.2.1
  obtain ⟨hBL, hBH, hIRL, hIRH, ⟨-, hmono⟩, -, -, -, -⟩ := hF
  have hbL0 : 0 ≤ bL := by linarith
  have hq : utility P q bL bH i t b' ≤ utility P q bL bH i t (if t then bL else bH) := by
    cases t
    · simpa using hBH i b' hb'
    · simpa using hBL i b' hb'
  have heq : utility P q bL bH i t (if t then bL else bH)
      = utility P (kSR k bL bH) bL bH i t (if t then bL else bH) := by
    unfold utility
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [update_price]
    simp only [alloc, assortSet, hmatch]
  have hct : cost P t ≤ (if t then bL else bH) := by
    cases t <;> simp [cost] <;> assumption
  have hUk := U_nonneg P hP (kSR k bL bH) bL bH i (if t then bL else bH)
  have hnn : 0 ≤ utility P (kSR k bL bH) bL bH i t (if t then bL else bH) := by
    rw [utility_eq]; exact mul_nonneg (by linarith) hUk
  rcases lt_or_ge b' (cost P t) with h1 | h1
  · rw [utility_eq]
    have := U_nonneg P hP (kSR k bL bH) bL bH i b'
    have : (b' - cost P t) * U P (kSR k bL bH) bL bH i b' ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) this
    linarith
  rcases lt_or_ge bH b' with h2 | h2
  · have hU0 : U P (kSR k bL bH) bL bH i b' = 0 := by
      unfold U
      refine Finset.sum_eq_zero (fun θ _ => ?_)
      have hni : i ∉ assortSet (kSR k bL bH) (Function.update (price bL bH θ) i b') := by
        simp [assortSet, kSR, h2]
      unfold alloc
      rw [demand_zero_of_not_mem P _ _ i hni, mul_zero]
    rw [utility_eq, hU0, mul_zero]
    exact hnn
  · have hUle : U P (kSR k bL bH) bL bH i b' ≤ U P q bL bH i b' := by
      unfold U
      exact Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left
        (alloc_kSR_le P hP q hmono k bL bH hbL0 hle hmatch θ i b' hb' h2)
        (weight_pos P hP θ).le)
    have : utility P (kSR k bL bH) bL bH i t b' ≤ utility P q bL bH i t b' := by
      rw [utility_eq, utility_eq]
      exact mul_le_mul_of_nonneg_left hUle (by linarith)
    linarith

theorem prop1 (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (r bL bH : ℝ) (hopt : IsOptimal8 P q r bL bH) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      IsOptimal8 P (kSR k bL bH) bH bL bH ∧
      ECS P (kSR k bL bH) bL bH = ECS P q bL bH := by
  have hF := hopt.1
  have hle := lemma3_of_feasible P hP q r bL bH hF
  obtain ⟨k, hk1, hkn, hmatch⟩ := matching P hP q r bL bH hF
  have hθL := hP.2.2.2.2.1
  have hIRL := hF.2.2.1
  have hIRH := hF.2.2.2.1
  have hbL0 : 0 ≤ bL := by linarith
  have hbH0 : 0 ≤ bH := by linarith
  have hECS : ECS P (kSR k bL bH) bL bH = ECS P q bL bH := by
    unfold ECS
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    simp only [alloc, assortSet, hmatch θ]
  have hTD := kSR_TD (n := n) k bL bH hk1 hle
  refine ⟨k, hk1, hkn, ⟨⟨?_, ?_, hIRL, hIRH, ⟨kSR_anon k bL bH, kSR_mono k bL bH⟩,
    kSR_RP1 k bL bH, hIRH, hTD, ?_⟩, ?_⟩, hECS⟩
  · intro i b' hb'
    simpa using kSR_BN P hP q r bL bH hF k hle hmatch true i b' hb'
  · intro i b' hb'
    simpa using kSR_BN P hP q r bL bH hF k hle hmatch false i b' hb'
  · intro θ
    obtain ⟨j, hj⟩ := hTD (price bL bH θ) (price_nonneg hbL0 hbH0 θ)
      ⟨⟨0, hP.1⟩, by simp only [price]; split_ifs <;> linarith⟩
    exact ⟨j, by simp [assortSet, hj]⟩
  · intro q' r' bL' bH' hF'
    rw [hECS]
    exact hopt.2 q' r' bL' bH' hF'

end PayAsBid.SoftReserve.Aux

open PayAsBid.SoftReserve in
theorem solution {n : ℕ} (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (r bL bH : ℝ) (hopt : IsOptimal8 P q r bL bH) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      IsOptimal8 P (kSR k bL bH) bH bL bH ∧
      ECS P (kSR k bL bH) bL bH = ECS P q bL bH :=
  PayAsBid.SoftReserve.Aux.prop1 P hP q r bL bH hopt

