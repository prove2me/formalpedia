-- Prove2me | solution 1 for WildeQIT.Compression.theorem_14_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T14:31:15.395184+00:00
-- url     : https://prove2.me/submissions/7a020d8e-a204-46dc-be22-4f84b267f2b8

import Mathlib
import Definitions.Def_WildeQIT_sourceCode
import Definitions.Def_WildeQIT_entropy

set_option autoImplicit false

namespace WildeQIT.ShannonAux

open Finset

variable {α : Type} [Fintype α]

lemma sum_succ_fun (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → α, f (Fin.cons a x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma iid_one (p : FinDist α) (n : ℕ) : ∑ x : Fin n → α, ∏ i, p.prob (x i) = 1 := by
  simpa using (p.iid n).sum_eq_one

/-- Centered information density `-log₂ p(a) - H(p)`. -/
noncomputable def hfun (p : FinDist α) (a : α) : ℝ := -Real.logb 2 (p.prob a) - entropy p

lemma hfun_mean (p : FinDist α) : ∑ a, p.prob a * hfun p a = 0 := by
  have : ∑ a, p.prob a * hfun p a
      = ∑ a, -(p.prob a * Real.logb 2 (p.prob a)) - (∑ a, p.prob a) * entropy p := by
    unfold hfun
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [this, p.sum_eq_one, Finset.sum_neg_distrib]
  unfold entropy
  ring

lemma iid_mean (p : FinDist α) (h : α → ℝ) (hm : ∑ a, p.prob a * h a = 0) (n : ℕ) :
    ∑ x : Fin n → α, (∏ i, p.prob (x i)) * ∑ i, h (x i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → α, (p.prob a * ∏ i, p.prob (x i)) * (h a + ∑ i, h (x i))
        = p.prob a * h a := by
      intro a
      calc _ = p.prob a * h a * ∑ x : Fin n → α, ∏ i, p.prob (x i)
              + p.prob a * ∑ x : Fin n → α, (∏ i, p.prob (x i)) * ∑ i, h (x i) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, hm]

lemma iid_var (p : FinDist α) (h : α → ℝ) (hm : ∑ a, p.prob a * h a = 0) (n : ℕ) :
    ∑ x : Fin n → α, (∏ i, p.prob (x i)) * (∑ i, h (x i)) ^ 2
      = n * ∑ a, p.prob a * h a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → α, (p.prob a * ∏ i, p.prob (x i)) * (h a + ∑ i, h (x i)) ^ 2
        = p.prob a * h a ^ 2 + p.prob a * (n * ∑ a, p.prob a * h a ^ 2) := by
      intro a
      calc _ = p.prob a * h a ^ 2 * ∑ x : Fin n → α, ∏ i, p.prob (x i)
              + 2 * p.prob a * h a * ∑ x : Fin n → α, (∏ i, p.prob (x i)) * ∑ i, h (x i)
              + p.prob a * ∑ x : Fin n → α, (∏ i, p.prob (x i)) * (∑ i, h (x i)) ^ 2 := by
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
                  ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one, iid_mean p h hm, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, ← Finset.sum_mul,
      p.sum_eq_one]
    push_cast
    ring

lemma cheb (p : FinDist α) (h : α → ℝ) (hm : ∑ a, p.prob a * h a = 0) (n : ℕ) (t : ℝ)
    (ht : 0 < t) :
    ∑ x ∈ univ.filter (fun x : Fin n → α => t ≤ |∑ i, h (x i)|), (p.iid n).prob x
      ≤ (n * ∑ a, p.prob a * h a ^ 2) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity), ← iid_var p h hm n, Finset.sum_mul]
  calc _ ≤ ∑ x ∈ univ.filter (fun x : Fin n → α => t ≤ |∑ i, h (x i)|),
        (∏ i, p.prob (x i)) * (∑ i, h (x i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        rw [FinDist.iid_prob]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => p.nonneg (x i))
        have h2 := hx.2
        nlinarith [mul_le_mul h2 h2 ht.le (abs_nonneg _), sq_abs (∑ i, h (x i))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg (x i)) (sq_nonneg _))

lemma prob_eq (p : FinDist α) (n : ℕ) (x : Fin n → α) (hx : 0 < (p.iid n).prob x) :
    (p.iid n).prob x = (2 : ℝ) ^ (-(∑ i, hfun p (x i)) - n * entropy p) := by
  have hne : ∀ i ∈ (univ : Finset (Fin n)), p.prob (x i) ≠ 0 := by
    rw [FinDist.iid_prob] at hx
    exact Finset.prod_ne_zero_iff.mp (ne_of_gt hx)
  calc (p.iid n).prob x = (2 : ℝ) ^ Real.logb 2 ((p.iid n).prob x) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ = _ := by
        congr 1
        rw [FinDist.iid_prob, Real.logb_prod _ _ hne]
        unfold hfun
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

omit [Fintype α] in
lemma code_of_finset {n : ℕ} (T : Finset (Fin n → α)) (hT : T.Nonempty) :
    ∃ c : SourceCode α n T.card, ∀ x ∈ T, c.dec (c.enc x) = x := by
  classical
  obtain ⟨x0, hx0⟩ := hT
  refine ⟨⟨fun x => if hx : x ∈ T then T.equivFin ⟨x, hx⟩ else T.equivFin ⟨x0, hx0⟩,
    fun i => (T.equivFin.symm i).1⟩, fun x hx => ?_⟩
  simp [hx]

lemma var_nonneg (p : FinDist α) (h : α → ℝ) : 0 ≤ ∑ a, p.prob a * h a ^ 2 :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (sq_nonneg _)

theorem direct [DecidableEq α] (p : FinDist α) : IsAchievableSourceRate p (entropy p) := by
  intro ε hε hε1 δ hδ
  have hm := hfun_mean p
  have hV := var_nonneg p (hfun p)
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ a, p.prob a * hfun p a ^ 2) / (ε * δ ^ 2))
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
  set V := ∑ a, p.prob a * hfun p a ^ 2 with hVdef
  set T := univ.filter (fun x : Fin n → α =>
    0 < (p.iid n).prob x ∧ |∑ i, hfun p (x i)| < n * δ) with hTdef
  have hbad : ∑ x ∈ univ.filter (fun x => x ∉ T), (p.iid n).prob x ≤ ε := by
    have h1 : ∑ x ∈ univ.filter (fun x => x ∉ T), (p.iid n).prob x ≤
        ∑ x ∈ univ.filter (fun x : Fin n → α => n * δ ≤ |∑ i, hfun p (x i)|),
          (p.iid n).prob x := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x _
      by_cases hxT : x ∈ T
      · rw [if_neg (not_not.mpr hxT)]
        split_ifs
        · exact (p.iid n).nonneg x
        · exact le_rfl
      · rw [if_pos hxT]
        split_ifs with h2
        · exact le_rfl
        · have h4 : ¬ 0 < (p.iid n).prob x := fun h5 => hxT (by
              simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨h5, lt_of_not_ge h2⟩)
          exact le_of_not_gt h4
    have h2 := cheb p (hfun p) hm n (n * δ) (by positivity)
    have h3 : (n : ℝ) * V / (n * δ) ^ 2 ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      have h4 := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε * δ ^ 2)).mp hN
      have h5 : V ≤ ε * δ ^ 2 * n := by nlinarith [mul_pos hε (pow_pos hδ 2)]
      nlinarith
    linarith
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    have : univ.filter (fun x : Fin n → α => x ∉ T) = univ := by
      rw [hT]; ext x; simp
    rw [this, (p.iid n).sum_eq_one] at hbad
    linarith
  refine ⟨T.card, ?_, ?_⟩
  · -- counting bound
    have hlow : ∀ x ∈ T, (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ))) ≤ (p.iid n).prob x := by
      intro x hx
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [prob_eq p n x hx.1]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have := (abs_lt.mp hx.2).2
      nlinarith
    have hsum : (T.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ))) ≤ 1 := by
      calc (T.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ)))
          = ∑ x ∈ T, (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ T, (p.iid n).prob x := Finset.sum_le_sum hlow
        _ ≤ ∑ x, (p.iid n).prob x :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun x _ _ => (p.iid n).nonneg x)
        _ = 1 := (p.iid n).sum_eq_one
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv,
      div_le_one (Real.rpow_pos_of_pos (by norm_num) _)] at hsum
    exact hsum
  · obtain ⟨c, hc⟩ := code_of_finset T hTne
    refine ⟨c, le_trans ?_ hbad⟩
    unfold SourceCode.errorProb
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x ∈ T
    · rw [if_pos (hc x hx), if_neg (not_not.mpr hx)]
    · rw [if_pos hx]
      split_ifs
      · exact (p.iid n).nonneg x
      · exact le_rfl

theorem converse [DecidableEq α] (p : FinDist α) (R : ℝ) (hR : IsAchievableSourceRate p R) :
    entropy p ≤ R := by
  by_contra hlt
  rw [not_le] at hlt
  set η := (entropy p - R) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hRη : R = entropy p - 3 * η := by rw [hη]; ring
  have hm := hfun_mean p
  have hV := var_nonneg p (hfun p)
  set V := ∑ a, p.prob a * hfun p a ^ 2 with hVdef
  obtain ⟨N, hN⟩ := hR (1 / 2) (by norm_num) (by norm_num) η hηpos
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * V / η ^ 2 + 2 / η)
  set n := max N K with hn
  obtain ⟨M, hM, c, hc⟩ := hN n (le_max_left _ _)
  have hnK : (K : ℝ) ≤ n := by exact_mod_cast le_max_right N K
  have h4V : 0 ≤ 4 * V / η ^ 2 := by positivity
  have h2η : 0 < 2 / η := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  set Sx := univ.filter (fun x : Fin n → α => c.dec (c.enc x) = x) with hSx
  have hsucc : 1 / 2 ≤ ∑ x ∈ Sx, (p.iid n).prob x := by
    have : ∑ x ∈ Sx, (p.iid n).prob x + c.errorProb p = 1 := by
      unfold SourceCode.errorProb
      rw [hSx, Finset.sum_filter, ← Finset.sum_add_distrib, ← (p.iid n).sum_eq_one]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    linarith
  have hcard : (Sx.card : ℝ) ≤ M := by
    have : Sx.card ≤ M := by
      calc Sx.card ≤ (univ : Finset (Fin M)).card :=
            Finset.card_le_card_of_injOn c.enc (by intro x _; simp) (by
              intro x hx y hy hxy
              simp only [hSx, Finset.coe_filter, Finset.mem_univ, true_and,
                Set.mem_ofPred_eq] at hx hy
              calc x = c.dec (c.enc x) := hx.symm
                _ = c.dec (c.enc y) := by rw [hxy]
                _ = y := hy)
        _ = M := by simp
    exact_mod_cast this
  rw [← Finset.sum_filter_add_sum_filter_not Sx
    (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η)] at hsucc
  -- typical part
  have hA : ∑ x ∈ Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η),
      (p.iid n).prob x ≤ 1 / 4 := by
    have hup : ∀ x ∈ Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η),
        (p.iid n).prob x ≤ (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η))) := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rcases ((p.iid n).nonneg x).lt_or_eq with hpos | hzero
      · rw [prob_eq p n x hpos]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := (abs_lt.mp hx.2).1
        nlinarith
      · rw [← hzero]
        exact (Real.rpow_pos_of_pos (by norm_num) _).le
    have hc1 : ((Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η)).card : ℝ)
        ≤ M := by
      have := Finset.card_filter_le Sx (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η)
      have : (((Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η)).card : ℕ) : ℝ)
          ≤ Sx.card := by exact_mod_cast this
      linarith
    have hpow : (2 : ℝ) ^ ((n : ℝ) * (R + η)) * (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η)))
        ≤ 1 / 4 := by
      rw [← Real.rpow_add (by norm_num)]
      have hexp : (n : ℝ) * (R + η) + -((n : ℝ) * (entropy p - η)) = -((n : ℝ) * η) := by
        rw [hRη]; ring
      rw [hexp]
      have hnη : 2 ≤ (n : ℝ) * η := by
        have : 2 / η < n := by linarith
        have := (div_lt_iff₀ hηpos).mp this
        linarith
      calc (2 : ℝ) ^ (-((n : ℝ) * η)) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 4 := by rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    have hq := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-((n : ℝ) * (entropy p - η)))
    calc _ ≤ ∑ x ∈ Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η),
          (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η))) := Finset.sum_le_sum hup
      _ = ((Sx.filter (fun x : Fin n → α => |∑ i, hfun p (x i)| < n * η)).card : ℝ)
          * (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η))) :=
            mul_le_mul_of_nonneg_right hc1 hq.le
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R + η)) * (2 : ℝ) ^ (-((n : ℝ) * (entropy p - η))) :=
            mul_le_mul_of_nonneg_right hM hq.le
      _ ≤ 1 / 4 := hpow
  -- atypical part
  have hB : ∑ x ∈ Sx.filter (fun x : Fin n → α => ¬ |∑ i, hfun p (x i)| < n * η),
      (p.iid n).prob x < 1 / 4 := by
    have h1 : ∑ x ∈ Sx.filter (fun x : Fin n → α => ¬ |∑ i, hfun p (x i)| < n * η),
        (p.iid n).prob x ≤
        ∑ x ∈ univ.filter (fun x : Fin n → α => n * η ≤ |∑ i, hfun p (x i)|),
          (p.iid n).prob x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx ⊢
        exact hx.2
      · intro x _ _
        exact (p.iid n).nonneg x
    have h2 := cheb p (hfun p) hm n (n * η) (by positivity)
    have h3 : (n : ℝ) * V / (n * η) ^ 2 < 1 / 4 := by
      rw [div_lt_iff₀ (by positivity)]
      have h4 : 4 * V / η ^ 2 < n := by linarith
      have h5 := (div_lt_iff₀ (by positivity : (0 : ℝ) < η ^ 2)).mp h4
      nlinarith
    linarith
  linarith

end WildeQIT.ShannonAux

open WildeQIT in
theorem solution {α : Type} [Fintype α] [DecidableEq α] (p : FinDist α) :
    sInf {R : ℝ | IsAchievableSourceRate p R} = entropy p := by
  apply IsLeast.csInf_eq
  exact ⟨WildeQIT.ShannonAux.direct p, fun R hR => WildeQIT.ShannonAux.converse p R hR⟩
