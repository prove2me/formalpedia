-- Prove2me | solution 1 for PayAsBid.SoftReserve.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:41:55.394677+00:00
-- url     : https://prove2.me/submissions/a96d77f7-f5c0-444b-852b-2e27432763fa

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

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

lemma demand_unique (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (p x y : Fin n → ℝ)
    (hx : IsDemand P Q p x) (hy : IsDemand P Q p y) : x = y := by
  have hK : 0 < P.ro + P.rc := by linarith [hP.2.1, hP.2.2.1]
  set m : Fin n → ℝ := fun i => (x i + y i) / 2 with hm
  have hmA : Admissible Q m := by
    refine ⟨?_, fun i => ?_, fun i hi => ?_⟩
    · simp only [hm, ← Finset.sum_div, Finset.sum_add_distrib, hx.1.1, hy.1.1]; norm_num
    · simp only [hm]; linarith [hx.1.2.1 i, hy.1.2.1 i]
    · simp only [hm, hx.1.2.2 i hi, hy.1.2.2 i hi]; norm_num
  have h1 := (CS_le_iff P hP Q p x m hx.1 hmA).1 (hx.2 m hmA)
  have h2 := (CS_le_iff P hP Q p x y hx.1 hy.1).1 (hx.2 y hy.1)
  have h3 := (CS_le_iff P hP Q p y x hy.1 hx.1).1 (hy.2 x hx.1)
  unfold Fobj at h1 h2 h3
  have hsq : ∑ i, m i ^ 2 = (∑ i, x i ^ 2 + ∑ i, y i ^ 2) / 2 - (∑ i, (x i - y i) ^ 2) / 4 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hm]; ring)
  have hlin : ∑ i, p i * m i = (∑ i, p i * x i + ∑ i, p i * y i) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hm]; ring)
  rw [hsq, hlin] at h1
  have hD : ∑ i, (x i - y i) ^ 2 ≤ 0 := by
    generalize ∑ i, x i ^ 2 = A at h1 h2 h3
    generalize ∑ i, y i ^ 2 = B at h1 h2 h3
    generalize ∑ i, p i * x i = Cx at h1 h2 h3
    generalize ∑ i, p i * y i = Cy at h1 h2 h3
    generalize ∑ i, (x i - y i) ^ 2 = E at h1 ⊢
    have e : -((1 / 2) * ((A + B) / 2 - E / 4) / (P.ro + P.rc)) - (Cx + Cy) / 2
        = ((-((1 / 2) * A / (P.ro + P.rc)) - Cx) + (-((1 / 2) * B / (P.ro + P.rc)) - Cy)) / 2
          + E / (8 * (P.ro + P.rc)) := by field_simp; ring
    rw [e] at h1
    have : E / (8 * (P.ro + P.rc)) ≤ 0 := by linarith
    have h8 : 0 < 8 * (P.ro + P.rc) := by linarith
    by_contra hE; push Not at hE
    have := div_pos hE h8
    linarith
  have hz : ∀ i ∈ Finset.univ, (x i - y i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1
      (le_antisymm hD (Finset.sum_nonneg fun i _ => sq_nonneg _))
  ext i
  have := hz i (Finset.mem_univ i)
  have : x i - y i = 0 := by simpa using this
  linarith

theorem well_posed (P : Params n) (hP : P.Standing)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (p : Fin n → ℝ) :
    ∃! x, IsDemand P Q p x := by
  obtain ⟨x, hx⟩ := exists_demand P hP Q hQ p
  exact ⟨x, hx, fun y hy => demand_unique P hP Q p y x hy hx⟩

theorem lemma2 (P : Params n) (hP : P.Standing) :
    let P' : Params n := { P with a := 0, ro := P.ro + P.rc, rc := 0 }
    P'.Standing ∧
    (∀ Q : Finset (Fin n), Q.Nonempty → ∀ p : Fin n → ℝ, Nonneg p →
      ∀ x : Fin n → ℝ, IsDemand P Q p x ↔ IsDemand P' Q p x) ∧
    ∃ C : ℝ, ∀ p x : Fin n → ℝ, ∑ i, x i = 1 → CS P x p = CS P' x p + C := by
  intro P'
  have hP0 := hP
  obtain ⟨hn, hro, hrc, -, hθL, hθLH, hf0, hf1⟩ := hP
  have hP' : P'.Standing := by
    refine ⟨hn, by simp only [P']; linarith, le_rfl, ?_, hθL, hθLH, hf0, hf1⟩
    have : P'.Γ = Matrix.diagonal (fun _ => P.ro + P.rc) := by
      ext i j
      simp only [Params.Γ, Matrix.diagonal_apply, P']
      split_ifs <;> simp
    rw [this, Matrix.posDef_diagonal_iff]
    intro _; linarith
  have hF : ∀ p y, Fobj P' p y = Fobj P p y := by
    intro p y; simp [Fobj, P']
  refine ⟨hP', fun Q _ p _ x => ?_, ?_⟩
  · constructor
    · intro h
      refine ⟨h.1, fun y hy => ?_⟩
      rw [CS_le_iff P' hP' Q p x y h.1 hy, hF, hF]
      exact (CS_le_iff P hP0 Q p x y h.1 hy).1 (h.2 y hy)
    · intro h
      refine ⟨h.1, fun y hy => ?_⟩
      rw [CS_le_iff P hP0 Q p x y h.1 hy, ← hF, ← hF]
      exact (CS_le_iff P' hP' Q p x y h.1 hy).1 (h.2 y hy)
  · refine ⟨(P.a / (P.ro - ((n : ℝ) - 1) * P.rc)
      - (1/2) * (P.rc / (P.ro - ((n : ℝ) - 1) * P.rc)) / (P.ro + P.rc))
      - (P'.a / (P'.ro - ((n : ℝ) - 1) * P'.rc)
      - (1/2) * (P'.rc / (P'.ro - ((n : ℝ) - 1) * P'.rc)) / (P'.ro + P'.rc)), fun p x hx => ?_⟩
    rw [CS_simplex P hP0 x p hx, CS_simplex P' hP' x p hx]
    simp only [P', add_zero]
    ring

lemma demand_empty (P : Params n) (p : Fin n → ℝ) : demand P ∅ p = 0 := by
  unfold demand
  rw [dif_neg]
  rintro ⟨x, hx, -⟩
  have : ∑ i, x i = 0 := Finset.sum_eq_zero (fun i _ => hx.2.2 i (Finset.notMem_empty i))
  rw [hx.1] at this
  norm_num at this

lemma demand_perm (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    demand P (Finset.univ.filter fun j => σ j ∈ Q) (p ∘ σ) = demand P Q p ∘ σ := by
  set x := demand P Q p
  have hx := demand_spec P hP Q hQ p
  set Q' := Finset.univ.filter fun j => σ j ∈ Q
  have hQ' : Q'.Nonempty := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨σ.symm j, by simp [Q', hj]⟩
  have hFs : ∀ (y q : Fin n → ℝ), Fobj P (q ∘ σ) (y ∘ σ) = Fobj P q y := by
    intro y q
    unfold Fobj
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp σ (fun i => y i ^ 2), Equiv.sum_comp σ (fun i => q i * y i)]
  have hadm : ∀ y, Admissible Q y → Admissible Q' (y ∘ σ) := by
    intro y hy
    refine ⟨?_, fun i => hy.2.1 _, fun i hi => hy.2.2 _ (by simpa [Q'] using hi)⟩
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp σ y]; exact hy.1
  have hxd : IsDemand P Q' (p ∘ σ) (x ∘ σ) := by
    refine ⟨hadm x hx.1, fun y hy => ?_⟩
    have hyA : Admissible Q (y ∘ σ.symm) := by
      refine ⟨?_, fun i => hy.2.1 _, fun i hi => hy.2.2 _ (by simpa [Q'] using hi)⟩
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp σ.symm y]; exact hy.1
    rw [CS_le_iff P hP Q' (p ∘ σ) (x ∘ σ) y (hadm x hx.1) hy, hFs]
    have := (CS_le_iff P hP Q p x _ hx.1 hyA).1 (hx.2 _ hyA)
    have e : y = (y ∘ σ.symm) ∘ σ := by ext i; simp
    rw [e, hFs]; exact this
  exact demand_unique P hP Q' _ _ _ (demand_spec P hP Q' hQ' _) hxd

lemma demand_price_mono (P : Params n) (hP : P.Standing) (Q : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ Q) (p : Fin n → ℝ) (c : ℝ) (hc : c ≤ p i) :
    demand P Q p i ≤ demand P Q (Function.update p i c) i := by
  have hK : 0 < P.ro + P.rc := by linarith [hP.2.1, hP.2.2.1]
  have hQ : Q.Nonempty := ⟨i, hi⟩
  set p' := Function.update p i c
  set x := demand P Q p
  set y := demand P Q p'
  have hx := demand_spec P hP Q hQ p
  have hy := demand_spec P hP Q hQ p'
  by_contra hcon
  push Not at hcon
  have hxi : 0 < x i := lt_of_le_of_lt (demand_nonneg P Q p' i) hcon
  have hle : ∀ l ∈ Q, y l ≤ x l := by
    intro l hl
    by_contra h
    push Not at h
    have hli : l ≠ i := by rintro rfl; linarith
    have hyl : 0 < y l := lt_of_le_of_lt (demand_nonneg P Q p l) h
    have f1 := foc P hP Q p' y hy l i hi hyl
    have f2 := foc P hP Q p x hx i l hl hxi
    have hp'i : p' i = c := by simp [p']
    have hp'l : p' l = p l := by simp [p', Function.update_of_ne hli]
    rw [hp'i, hp'l] at f1
    have : y i / (P.ro + P.rc) < x i / (P.ro + P.rc) := div_lt_div_of_pos_right hcon hK
    have : y l / (P.ro + P.rc) < x l / (P.ro + P.rc) := by linarith
    have : y l < x l := (div_lt_div_iff_of_pos_right hK).1 this
    linarith
  have hsy : ∑ l ∈ Q, y l = 1 := by
    rw [← hy.1.1]
    exact Finset.sum_subset (Finset.subset_univ Q) (fun l _ hl => hy.1.2.2 l hl)
  have hsx : ∑ l ∈ Q, x l = 1 := by
    rw [← hx.1.1]
    exact Finset.sum_subset (Finset.subset_univ Q) (fun l _ hl => hx.1.2.2 l hl)
  have : ∑ l ∈ Q, y l < ∑ l ∈ Q, x l := Finset.sum_lt_sum hle ⟨i, hi, hcon⟩
  linarith

theorem alloc_anon_mono (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (hq : IsEquitable q) :
    (∀ b : Fin n → ℝ, Nonneg b → ∀ σ : Equiv.Perm (Fin n),
      alloc P q (b ∘ σ) = alloc P q b ∘ σ) ∧
    (∀ b : Fin n → ℝ, Nonneg b → ∀ (i : Fin n) (b' : ℝ), 0 ≤ b' → b' < b i →
      alloc P q b i ≤ alloc P q (Function.update b i b') i) := by
  obtain ⟨hanon, hmono⟩ := hq
  refine ⟨fun b hb σ => ?_, fun b hb i b' hb' hlt => ?_⟩
  · have hset : assortSet q (b ∘ σ) = Finset.univ.filter fun j => σ j ∈ assortSet q b := by
      ext j
      simp [assortSet, hanon σ b hb]
    unfold alloc
    rw [hset]
    by_cases hQ : (assortSet q b).Nonempty
    · exact demand_perm P hP _ hQ b σ
    · rw [Finset.not_nonempty_iff_eq_empty] at hQ
      rw [hQ]
      have he : (Finset.univ.filter fun j => σ j ∈ (∅ : Finset (Fin n))) = ∅ := by simp
      rw [he, demand_empty, demand_empty]
      rfl
  · obtain ⟨h1, h2⟩ := hmono b hb i b' hb' hlt
    by_cases hi : q b i = true
    · have hi2 : q (Function.update b i b') i = true := by rw [hi] at h1; revert h1; cases q (Function.update b i b') i <;> decide
      have hsub : assortSet q (Function.update b i b') ⊆ assortSet q b := by
        intro j hj
        simp only [assortSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_cases hji : j = i
        · subst hji; exact hi
        · have := h2 j hji; rw [hj] at this; revert this; cases q b j <;> decide
      have hiQ : i ∈ assortSet q b := by simp [assortSet, hi]
      have hiQ2 : i ∈ assortSet q (Function.update b i b') := by simp [assortSet, hi2]
      unfold alloc
      calc demand P (assortSet q b) b i
          ≤ demand P (assortSet q b) (Function.update b i b') i :=
            demand_price_mono P hP _ i hiQ b b' hlt.le
        _ ≤ demand P (assortSet q (Function.update b i b')) (Function.update b i b') i :=
            demand_antitone P hP _ _ i hiQ2 hsub _
    · have : i ∉ assortSet q b := by simp [assortSet, hi]
      unfold alloc
      rw [demand_zero_of_not_mem P _ _ i this]
      exact demand_nonneg P _ _ i

end PayAsBid.SoftReserve.Aux

open PayAsBid.SoftReserve in
theorem solution {n : ℕ} (P : Params n) (hP : P.Standing) :
    let P' : Params n := { P with a := 0, ro := P.ro + P.rc, rc := 0 }
    P'.Standing ∧
    (∀ Q : Finset (Fin n), Q.Nonempty → ∀ p : Fin n → ℝ, Nonneg p →
      ∀ x : Fin n → ℝ, IsDemand P Q p x ↔ IsDemand P' Q p x) ∧
    ∃ C : ℝ, ∀ p x : Fin n → ℝ, ∑ i, x i = 1 → CS P x p = CS P' x p + C :=
  PayAsBid.SoftReserve.Aux.lemma2 P hP
