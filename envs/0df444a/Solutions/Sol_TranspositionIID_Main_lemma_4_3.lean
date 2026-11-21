-- Prove2me | solution 1 for TranspositionIID.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:17:39.54918+00:00
-- url     : https://prove2.me/submissions/48ba34b6-ec85-4847-bdad-69cbe176a978

import Mathlib
import Definitions.Def_TranspositionIID_Main_Stationary
import Definitions.Def_TranspositionIID_Main_Perturbation

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Rev
open TranspositionIID.Main

variable {n : ℕ}

lemma kernel_nonneg (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) (a b : Equiv.Perm (Fin n)) :
    0 ≤ transpositionKernel q a b :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hq i]

lemma kernel_row (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) :
    ∑ b, transpositionKernel q a b = ∑ i, q i := by
  unfold transpositionKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma kernel_markov (q : Fin n → ℝ) (hq : ActuarialValuation.isFiniteStateDistribution q) :
    ActuarialValuation.isFiniteMarkovKernel (transpositionKernel q) :=
  ⟨kernel_nonneg q hq.1, fun a => by rw [kernel_row]; exact hq.2⟩

lemma pow_markov {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (t : ℕ) :
    (∀ a b, 0 ≤ (P ^ t) a b) ∧ ∀ a, ∑ b, (P ^ t) a b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> simp
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP.1 c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, (P ^ t) a c * P c b = ∑ c, (P ^ t) a c := by
            apply Finset.sum_congr rfl; intro c _
            rw [← Finset.mul_sum, hP.2 c, mul_one]
        _ = 1 := ih.2 a

lemma weight_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryWeight q a :=
  Finset.prod_pos fun i _ => pow_pos (hpos i) _

lemma partition_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) : 0 < partitionFunction q :=
  Finset.sum_pos (fun a _ => weight_pos q hpos a) Finset.univ_nonempty

end TranspositionIID.Main.Dev.Rev
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L43
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {n : ℕ}

lemma cost_le (p : Fin n → ℝ) (hp : ActuarialValuation.isFiniteStateDistribution p)
    (z : ListState n) : cost p z ≤ n := by
  calc cost p z = ∑ i, p i * (((z i).val + 1 : ℕ) : ℝ) := rfl
    _ ≤ ∑ i, p i * (n : ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hp.1 i)
        exact_mod_cast (z i).isLt
    _ = n := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma one_le_opt (p : Fin n → ℝ) (hp : ActuarialValuation.isFiniteStateDistribution p) :
    1 ≤ optimum p := by
  unfold optimum
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨z, rfl⟩
  calc (1 : ℝ) = ∑ i, p i * 1 := by simp [hp.2]
    _ ≤ cost p z := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hp.1 i)
        norm_cast; omega

lemma excess_le (p : Fin n → ℝ) (hp : ActuarialValuation.isFiniteStateDistribution p)
    (z : ListState n) : excess p z ≤ n := by
  unfold excess; linarith [cost_le p hp z, one_le_opt p hp]

lemma excess_nonneg' (p : Fin n → ℝ) (z : ListState n) : 0 ≤ excess p z := by
  unfold excess optimum
  exact sub_nonneg.2 (csInf_le (Set.finite_range _).bddBelow ⟨z, rfl⟩)

/-- Affine relation between the two costs. -/
lemma cost_affine (p : Fin n → ℝ) (c D : ℝ) (q : Fin n → ℝ) (hq : ∀ i, p i = D * q i - c)
    (σ : ListState n) :
    cost p σ = D * cost q σ - c * ∑ k : Fin n, (((k.val + 1 : ℕ)) : ℝ) := by
  have hS : ∑ i, (((σ i).val + 1 : ℕ) : ℝ) = ∑ k : Fin n, (((k.val + 1 : ℕ)) : ℝ) :=
    Equiv.sum_comp σ (fun k => (((k.val + 1 : ℕ)) : ℝ))
  unfold cost
  rw [← hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [hq i]; ring

lemma excess_affine (p : Fin n → ℝ) (c D : ℝ) (q : Fin n → ℝ) (hq : ∀ i, p i = D * q i - c)
    (hD : 0 ≤ D) (σ : ListState n) : excess p σ = D * excess q σ := by
  obtain ⟨σp, hσp⟩ := (Set.range_nonempty (cost p)).csInf_mem (Set.finite_range (cost p))
  obtain ⟨σq, hσq⟩ := (Set.range_nonempty (cost q)).csInf_mem (Set.finite_range (cost q))
  have h1 : optimum p ≤ cost p σq := csInf_le (Set.finite_range _).bddBelow ⟨σq, rfl⟩
  have h2 : optimum q ≤ cost q σp := csInf_le (Set.finite_range _).bddBelow ⟨σp, rfl⟩
  have e1 := cost_affine p c D q hq σq
  have e2 := cost_affine p c D q hq σp
  have hopt : optimum p = D * optimum q - c * ∑ k : Fin n, (((k.val + 1 : ℕ)) : ℝ) := by
    apply le_antisymm
    · have : optimum p ≤ cost p σq := h1
      rw [e1, hσq] at this; exact this
    · have h3 := mul_le_mul_of_nonneg_left h2 hD
      have : cost p σp = optimum p := hσp
      rw [e2] at this
      linarith
  unfold excess
  rw [cost_affine p c D q hq σ, hopt]; ring

lemma row_diff (p q : Fin n → ℝ) (a : ListState n) :
    ∑ b, |transpositionKernel p a b - transpositionKernel q a b| ≤ ∑ i, |p i - q i| := by
  have h : ∀ b, transpositionKernel p a b - transpositionKernel q a b =
      ∑ i, (if transposeRequest a i = b then p i - q i else 0) := by
    intro b; unfold transpositionKernel
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  calc ∑ b, |transpositionKernel p a b - transpositionKernel q a b|
      ≤ ∑ b, ∑ i, |if transposeRequest a i = b then p i - q i else 0| := by
        apply Finset.sum_le_sum; intro b _
        rw [h b]; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |p i - q i| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        simp [apply_ite abs]

lemma l1_pow {S : Type*} [Fintype S] [DecidableEq S] (P Q : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (hQ : ActuarialValuation.isFiniteMarkovKernel Q)
    (ε : ℝ) (hε : ∀ a, ∑ b, |P a b - Q a b| ≤ ε) (s : S) (t : ℕ) :
    ∑ z, |(P ^ t) s z - (Q ^ t) s z| ≤ t * ε := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hd : ∀ b, (P ^ (t + 1)) s b - (Q ^ (t + 1)) s b =
        ∑ a, ((P ^ t) s a - (Q ^ t) s a) * P a b + ∑ a, (Q ^ t) s a * (P a b - Q a b) := by
      intro b; rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]; ring
    have hQt := Rev.pow_markov Q hQ t
    have hA : ∑ b, |∑ a, ((P ^ t) s a - (Q ^ t) s a) * P a b| ≤ t * ε := by
      calc ∑ b, |∑ a, ((P ^ t) s a - (Q ^ t) s a) * P a b|
          ≤ ∑ b, ∑ a, |(P ^ t) s a - (Q ^ t) s a| * P a b := by
            apply Finset.sum_le_sum; intro b _
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            apply Finset.sum_congr rfl; intro a _
            rw [abs_mul, abs_of_nonneg (hP.1 a b)]
        _ = ∑ a, |(P ^ t) s a - (Q ^ t) s a| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            rw [← Finset.mul_sum, hP.2 a, mul_one]
        _ ≤ t * ε := ih
    have hB : ∑ b, |∑ a, (Q ^ t) s a * (P a b - Q a b)| ≤ ε := by
      calc ∑ b, |∑ a, (Q ^ t) s a * (P a b - Q a b)|
          ≤ ∑ b, ∑ a, (Q ^ t) s a * |P a b - Q a b| := by
            apply Finset.sum_le_sum; intro b _
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            apply Finset.sum_congr rfl; intro a _
            rw [abs_mul, abs_of_nonneg (hQt.1 s a)]
        _ = ∑ a, (Q ^ t) s a * ∑ b, |P a b - Q a b| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.mul_sum]
        _ ≤ ∑ a, (Q ^ t) s a * ε :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hε a) (hQt.1 s a)
        _ = ε := by rw [← Finset.sum_mul, hQt.2 s, one_mul]
    calc ∑ z, |(P ^ (t + 1)) s z - (Q ^ (t + 1)) s z|
        = ∑ b, |∑ a, ((P ^ t) s a - (Q ^ t) s a) * P a b +
            ∑ a, (Q ^ t) s a * (P a b - Q a b)| := by simp_rw [hd]
      _ ≤ ∑ b, (|∑ a, ((P ^ t) s a - (Q ^ t) s a) * P a b| +
            |∑ a, (Q ^ t) s a * (P a b - Q a b)|) :=
          Finset.sum_le_sum fun b _ => abs_add_le _ _
      _ ≤ (t + 1 : ℕ) * ε := by
          rw [Finset.sum_add_distrib]; push_cast; linarith

lemma exp_diff {S : Type*} [Fintype S] [DecidableEq S] (P Q : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (hQ : ActuarialValuation.isFiniteMarkovKernel Q)
    (ε : ℝ) (hε : ∀ a, ∑ b, |P a b - Q a b| ≤ ε) (s : S) (t : ℕ) (F : S → ℝ) (B : ℝ)
    (h0 : ∀ z, 0 ≤ F z) (hB : ∀ z, F z ≤ B) :
    ∑ z, (P ^ t) s z * F z ≤ ∑ z, (Q ^ t) s z * F z + (B / 2) * (t * ε) := by
  have hPt := Rev.pow_markov P hP t
  have hQt := Rev.pow_markov Q hQ t
  have hl := l1_pow P Q hP hQ ε hε s t
  have e1 : ∑ z, (P ^ t) s z * F z - ∑ z, (Q ^ t) s z * F z =
      ∑ z, ((P ^ t) s z - (Q ^ t) s z) * (F z - B / 2) := by
    have : ∑ z, ((P ^ t) s z - (Q ^ t) s z) * (B / 2) = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hPt.2, hQt.2]; ring
    simp only [mul_sub, Finset.sum_sub_distrib, sub_mul] at this ⊢
    linarith
  have e2 : ∑ z, ((P ^ t) s z - (Q ^ t) s z) * (F z - B / 2) ≤
      ∑ z, |(P ^ t) s z - (Q ^ t) s z| * (B / 2) := by
    apply Finset.sum_le_sum; intro z _
    calc ((P ^ t) s z - (Q ^ t) s z) * (F z - B / 2)
        ≤ |((P ^ t) s z - (Q ^ t) s z) * (F z - B / 2)| := le_abs_self _
      _ = |(P ^ t) s z - (Q ^ t) s z| * |F z - B / 2| := abs_mul _ _
      _ ≤ |(P ^ t) s z - (Q ^ t) s z| * (B / 2) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [h0 z, hB z]
  rw [← Finset.sum_mul] at e2
  nlinarith [e1, e2, hl, show 0 ≤ B / 2 from by linarith [h0 s, hB s]]

lemma fact_le (m : ℕ) : ((Nat.factorial m : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * (m - 1) / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ((m : ℝ) + 1) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
    have h2 : ((Nat.factorial (m + 1) : ℕ) : ℝ) = ((m : ℝ) + 1) * ((Nat.factorial m : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [h2]
    calc ((m : ℝ) + 1) * ((Nat.factorial m : ℕ) : ℝ) ≤ Real.exp m * Real.exp ((m : ℝ) * (m - 1) / 2) :=
          mul_le_mul h1 ih (by positivity) (Real.exp_pos _).le
      _ = Real.exp (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) / 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

lemma exp_sum (σ : ListState n) : (∑ i : Fin n, (n - 1 - (σ i).val)) * 2 = n * (n - 1) := by
  rw [Equiv.sum_comp σ (fun k : Fin n => n - 1 - k.val),
    Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n,
    Finset.sum_range_reflect (fun k => k) n, Finset.sum_range_id_mul_two]

lemma n2e (hn : 2 ≤ n) : (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) ≤ 1 := by
  have hx : (0 : ℝ) ≤ n := by positivity
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  nlinarith [sq_nonneg ((n : ℝ) - 2), pow_nonneg hx 3]

lemma ceiling_bound (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p) :
    entropyCeiling (stationaryLaw (perturb p)) ≤ (n : ℝ) ^ 3 / 2 := by
  set c : ℝ := Real.exp (-(n : ℝ)) with hc
  set D : ℝ := 1 + (n : ℝ) * c with hD
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hc0 : 0 < c := Real.exp_pos _
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith
  have hD0 : 0 < D := by linarith
  have hqdef : ∀ i, perturb p i = (p i + c) / D := fun i => rfl
  have hq0 : ∀ i, 0 < perturb p i := fun i => by
    rw [hqdef]; exact div_pos (by linarith [hp.1 i]) hD0
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp.2]; exact Finset.single_le_sum (f := p) (fun j _ => hp.1 j) (Finset.mem_univ i)
  have hq1 : ∀ i, perturb p i ≤ 1 := fun i => by
    rw [hqdef, div_le_one hD0]; nlinarith [hp1 i]
  set r : ℝ := c / D with hr
  have hr0 : 0 < r := div_pos hc0 hD0
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hD0]; nlinarith [Real.exp_le_one_iff.2 (show -(n:ℝ) ≤ 0 by linarith)]
  have hrq : ∀ i, r ≤ perturb p i := fun i => by
    rw [hqdef, hr]; exact div_le_div_of_nonneg_right (by linarith [hp.1 i]) hD0.le
  obtain ⟨z0, hz0⟩ := (Set.range_nonempty (stationaryLaw (perturb p))).csInf_mem
    (Set.finite_range (stationaryLaw (perturb p)))
  unfold entropyCeiling
  rw [← hz0]
  have hZ : partitionFunction (perturb p) ≤ Real.exp ((n : ℝ) * (n - 1) / 2) := by
    calc partitionFunction (perturb p) ≤ ∑ σ : ListState n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro σ _
          unfold stationaryWeight
          apply Finset.prod_le_one (fun i _ => pow_nonneg (hq0 i).le _)
          intro i _; exact pow_le_one₀ (hq0 i).le (hq1 i)
      _ = ((Nat.factorial n : ℕ) : ℝ) := by simp [Fintype.card_perm]
      _ ≤ _ := fact_le n
  set N : ℕ := ∑ i : Fin n, (n - 1 - (z0 i).val) with hN
  have hNr : (N : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have h := exp_sum z0
    have : ((N * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by rw [← hN] at h; exact_mod_cast h
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this
    linarith
  have hw : r ^ N ≤ stationaryWeight (perturb p) z0 := by
    unfold stationaryWeight
    rw [hN, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun i _ => pow_nonneg hr0.le _)
    intro i _; exact pow_le_pow_left₀ hr0.le (hrq i) _
  have hwpos : 0 < r ^ N := pow_pos hr0 _
  have hZpos := Rev.partition_pos (perturb p) hq0
  have hinv : 1 / stationaryLaw (perturb p) z0 =
      partitionFunction (perturb p) / stationaryWeight (perturb p) z0 := by
    unfold stationaryLaw
    have := (Rev.weight_pos (perturb p) hq0 z0).ne'
    field_simp
  rw [hinv]
  have hle : partitionFunction (perturb p) / stationaryWeight (perturb p) z0 ≤
      Real.exp ((n : ℝ) * (n - 1) / 2) / r ^ N :=
    div_le_div₀ (Real.exp_pos _).le hZ hwpos hw
  have hpos1 : 0 < partitionFunction (perturb p) / stationaryWeight (perturb p) z0 :=
    div_pos hZpos (Rev.weight_pos (perturb p) hq0 z0)
  have hlog := Real.log_le_log hpos1 hle
  rw [Real.log_div (Real.exp_pos _).ne' hwpos.ne', Real.log_exp, Real.log_pow, hNr, hr,
    Real.log_div hc0.ne' hD0.ne', hc, Real.log_exp] at hlog
  refine hlog.trans ?_
  have hlogD : Real.log D ≤ (n : ℝ) * c := by
    have := Real.log_le_sub_one_of_pos hD0; rw [hD] at this ⊢; linarith
  have hkey : ((n : ℝ) - 1) * ((n : ℝ) * c) ≤ 1 := by
    have := n2e hn
    nlinarith [hc0]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * (n - 1) / 2 := by positivity
  have h3 : (n : ℝ) * (n - 1) / 2 * Real.log D ≤ (n : ℝ) / 2 := by
    calc (n : ℝ) * (n - 1) / 2 * Real.log D ≤ (n : ℝ) * (n - 1) / 2 * ((n : ℝ) * c) :=
          mul_le_mul_of_nonneg_left hlogD hn0
      _ = (n : ℝ) / 2 * (((n : ℝ) - 1) * ((n : ℝ) * c)) := by ring
      _ ≤ (n : ℝ) / 2 * 1 := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (n : ℝ) / 2 := by ring
  nlinarith [h3]

end TranspositionIID.Main.Dev.L43

namespace TranspositionIID.Main.Dev.L43
open TranspositionIID.Main

lemma coupling {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p) (σ : ListState n) (t : ℕ) :
    expectedAfter (transpositionKernel p) σ t (excess p) ≤
      expectedAfter (transpositionKernel (perturb p)) σ t (excess (perturb p)) +
        ((t : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) := by
  set c : ℝ := Real.exp (-(n : ℝ)) with hc
  set D : ℝ := 1 + (n : ℝ) * c with hD
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hc0 : 0 < c := Real.exp_pos _
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith
  have hD0 : 0 < D := by linarith
  have hqdef : ∀ i, perturb p i = (p i + c) / D := fun i => rfl
  have hqrel : ∀ i, p i = D * perturb p i - c := fun i => by
    rw [hqdef]; field_simp; ring
  have hqd : ActuarialValuation.isFiniteStateDistribution (perturb p) := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [hqdef]; exact div_nonneg (by linarith [hp.1 i]) hD0.le
    · simp only [hqdef]
      rw [← Finset.sum_div, Finset.sum_add_distrib, hp.2]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hD, add_comm]; exact div_self (by linarith)
  have hP := Rev.kernel_markov p hp
  have hQ := Rev.kernel_markov (perturb p) hqd
  set ε : ℝ := ∑ i, |p i - perturb p i| with hε
  have hεb : ε ≤ 2 * n * c := by
    have h1 : ∀ i, |p i - perturb p i| ≤ c * (n * p i + 1) := by
      intro i
      have e : p i - perturb p i = c * (n * p i - 1) / D := by
        rw [hqdef, hD]; field_simp; ring
      rw [e, abs_div, abs_of_pos hD0, div_le_iff₀ hD0, abs_mul, abs_of_pos hc0]
      have h2 : |(n : ℝ) * p i - 1| ≤ n * p i + 1 := by
        rw [abs_le]; constructor <;> nlinarith [hp.1 i]
      have h3 : 0 ≤ c * (n * p i + 1) := by have := hp.1 i; positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hc0.le]
    calc ε ≤ ∑ i, c * (n * p i + 1) := Finset.sum_le_sum fun i _ => h1 i
      _ = c * (n * ∑ i, p i + n) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]; simp
      _ = 2 * n * c := by rw [hp.2]; ring
  have hdiff := exp_diff (transpositionKernel p) (transpositionKernel (perturb p)) hP hQ ε
    (fun a => row_diff p (perturb p) a) σ t (excess p) n (excess_nonneg' p) (excess_le p hp)
  have hQt := Rev.pow_markov (transpositionKernel (perturb p)) hQ t
  have hEq : ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess p z =
      D * ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess (perturb p) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _
    rw [excess_affine p c D (perturb p) hqrel hD0.le z]; ring
  have hEn : ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess (perturb p) z ≤ n := by
    calc _ ≤ ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * (n : ℝ) :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (excess_le _ hqd z) (hQt.1 σ z)
      _ = n := by rw [← Finset.sum_mul, hQt.2 σ, one_mul]
  have hE0 : 0 ≤ ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess (perturb p) z :=
    Finset.sum_nonneg fun z _ => mul_nonneg (hQt.1 σ z) (excess_nonneg' _ z)
  show ∑ z, ((transpositionKernel p) ^ t) σ z * excess p z ≤
    ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess (perturb p) z + _
  set E := ∑ z, ((transpositionKernel (perturb p)) ^ t) σ z * excess (perturb p) z with hE
  have h1 : (n : ℝ) / 2 * (t * ε) ≤ t * n ^ 2 * c := by
    have : (n : ℝ) / 2 * (t * ε) ≤ (n : ℝ) / 2 * (t * (2 * n * c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεb (by positivity)) (by positivity)
    nlinarith [this]
  have h2 : D * E ≤ E + n ^ 2 * c := by
    rw [hD]
    have : (n : ℝ) * c * E ≤ (n : ℝ) * c * n :=
      mul_le_mul_of_nonneg_left hEn (by positivity)
    nlinarith [this]
  rw [hEq] at hdiff
  nlinarith [hdiff, h1, h2]

end TranspositionIID.Main.Dev.L43

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev

theorem chk_lemma_4_3 {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p) (hsort : Decreasing p) :
    ActuarialValuation.isFiniteStateDistribution (perturb p) ∧
    (∀ i, 0 < perturb p i) ∧
    (∀ i j, perturb p i ≤ perturb p j ↔ p i ≤ p j) ∧
    (∀ (σ : ListState n) (t : ℕ),
      expectedAfter (transpositionKernel p) σ t (excess p) ≤
        expectedAfter (transpositionKernel (perturb p)) σ t (excess (perturb p)) +
          ((t : ℝ) + 1) * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ))) ∧
    entropyCeiling (stationaryLaw (perturb p)) ≤ (n : ℝ) ^ 3 / 2 := by
  have hD0 : 0 < 1 + (n : ℝ) * Real.exp (-(n : ℝ)) := by positivity
  have hq0 : ∀ i, 0 < perturb p i := fun i =>
    div_pos (by linarith [hp.1 i, Real.exp_pos (-(n : ℝ))]) hD0
  refine ⟨?_, hq0, ?_, fun σ t => L43.coupling hn p hp σ t, L43.ceiling_bound hn p hp⟩
  · refine ⟨fun i => (hq0 i).le, ?_⟩
    show ∑ i, (p i + Real.exp (-(n : ℝ))) / (1 + (n : ℝ) * Real.exp (-(n : ℝ))) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [add_comm]; exact div_self (by rw [add_comm]; exact hD0.ne')
  · intro i j
    show (p i + Real.exp (-(n : ℝ))) / (1 + (n : ℝ) * Real.exp (-(n : ℝ))) ≤
      (p j + Real.exp (-(n : ℝ))) / (1 + (n : ℝ) * Real.exp (-(n : ℝ))) ↔ _
    rw [div_le_div_iff_of_pos_right hD0]; simp

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_lemma_4_3 := @TranspositionIID.Main.chk_lemma_4_3
