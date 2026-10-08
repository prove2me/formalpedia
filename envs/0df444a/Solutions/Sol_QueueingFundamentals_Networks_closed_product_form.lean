-- Prove2me | solution 1 for QueueingFundamentals.Networks.closed_product_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:20:07.526368+00:00
-- url     : https://prove2.me/submissions/fc2ca732-35f2-4e79-acf7-313ccfb3851f

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson



namespace QueueingFundamentals.Networks
open Finset

/-- move one customer from `a` to `b` -/
def mvC {k : ℕ} (n : Fin k → ℕ) (a b : Fin k) : Fin k → ℕ := (n + Pi.single b 1) - Pi.single a 1

lemma moveState_eq_mvC {k : ℕ} (n : Fin k → ℕ) (i j : Fin k) (h : i ≠ j) :
    moveState n i j = mvC n j i := by
  funext x
  simp only [moveState, mvC, Function.update_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hxi : x = i
  · subst hxi; simp [h]
  · by_cases hxj : x = j
    · subst hxj; simp [hxi]
    · simp [hxi, hxj]

lemma mvC_add {k : ℕ} (n : Fin k → ℕ) (a b : Fin k) (ha : 1 ≤ n a) :
    mvC n a b + Pi.single a 1 = n + Pi.single b 1 := by
  funext x
  simp only [mvC, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hxa : x = a
  · subst hxa; split_ifs <;> omega
  · split_ifs <;> omega

lemma mvC_self {k : ℕ} (n : Fin k → ℕ) (a : Fin k) : mvC n a a = n := by
  funext x; simp [mvC, Pi.single_apply]

lemma mvC_mvC {k : ℕ} (n : Fin k → ℕ) (a b c : Fin k) (ha : 1 ≤ n a) :
    mvC (mvC n a c) c b = mvC n a b := by
  funext x
  simp only [mvC, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hxa : x = a
  · subst hxa; split_ifs <;> omega
  · split_ifs <;> omega

lemma mem_states_iff {k N : ℕ} (n : Fin k → ℕ) : n ∈ states k N ↔ ∑ i, n i = N := by
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
    have := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le _) (Finset.mem_univ i); omega

lemma sum_add_single {k : ℕ} (n : Fin k → ℕ) (b : Fin k) :
    ∑ i, (n + (Pi.single b 1 : Fin k → ℕ)) i = ∑ i, n i + 1 := by
  simp [Finset.sum_add_distrib, Finset.sum_pi_single']

lemma mvC_mem {k N : ℕ} (n : Fin k → ℕ) (a b : Fin k) (hn : n ∈ states k N) (ha : 1 ≤ n a) :
    mvC n a b ∈ states k N := by
  rw [mem_states_iff] at *
  have h1 : ∑ i, (mvC n a b + (Pi.single a 1 : Fin k → ℕ)) i =
      ∑ i, (n + (Pi.single b 1 : Fin k → ℕ)) i := by rw [mvC_add n a b ha]
  rw [sum_add_single, sum_add_single] at h1; omega

lemma add_single_mem {k N : ℕ} (n : Fin k → ℕ) (b : Fin k) (hn : n ∈ states k N) :
    n + (Pi.single b 1 : Fin k → ℕ) ∈ states k (N + 1) := by
  rw [mem_states_iff] at *; rw [sum_add_single, hn]

/-- product weight -/
lemma prod_add_single {k : ℕ} (rho : Fin k → ℝ) (n : Fin k → ℕ) (b : Fin k) :
    ∏ i, rho i ^ (n + (Pi.single b 1 : Fin k → ℕ)) i = (∏ i, rho i ^ n i) * rho b := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single b]
  · simp
  · intro x _ hx; simp [Pi.single_apply, hx]
  · simp

lemma prod_pos' {k : ℕ} (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i) (n : Fin k → ℕ) :
    0 < ∏ i, rho i ^ n i := Finset.prod_pos fun i _ => pow_pos (hrho i) _

lemma states_nonempty {k : ℕ} [NeZero k] (N : ℕ) : (states k N).Nonempty := by
  refine ⟨Pi.single 0 N, ?_⟩
  rw [mem_states_iff]; simp [Finset.sum_pi_single']

lemma normConst_pos {k : ℕ} [NeZero k] (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i) (N : ℕ) :
    0 < normConst (fun i m => rho i ^ m) N :=
  Finset.sum_pos (fun n _ => prod_pos' rho hrho n) (states_nonempty N)

lemma pf_sum {k : ℕ} [NeZero k] (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i) (N : ℕ) :
    ∑ n ∈ states k N, productForm (fun i m => rho i ^ m) N n = 1 := by
  have hG := normConst_pos rho hrho N
  rw [Finset.sum_congr rfl fun n hn => by rw [productForm, if_pos hn], ← Finset.sum_div]
  exact div_self hG.ne'

lemma pf_mvC {k N : ℕ} (rho : Fin k → ℝ) (n : Fin k → ℕ) (a b : Fin k)
    (hn : n ∈ states k N) (ha : 1 ≤ n a) :
    productForm (fun i m => rho i ^ m) N (mvC n a b) * rho a =
      productForm (fun i m => rho i ^ m) N n * rho b := by
  simp only [productForm, if_pos hn, if_pos (mvC_mem n a b hn ha)]
  have h1 : ∏ i, rho i ^ (mvC n a b + (Pi.single a 1 : Fin k → ℕ)) i =
      ∏ i, rho i ^ (n + (Pi.single b 1 : Fin k → ℕ)) i := by rw [mvC_add n a b ha]
  rw [prod_add_single, prod_add_single] at h1
  rw [div_mul_eq_mul_div, h1, div_mul_eq_mul_div]

lemma pf_balance {k N : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (rho : Fin k → ℝ)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho)
    (n : Fin k → ℕ) (hn : n ∈ states k N) :
    BalanceAt mu R (productForm (fun i m => rho i ^ m) N) n := by
  unfold BalanceAt
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : 1 ≤ n j
  · rw [if_pos hj]
    have key : ∀ i ∈ univ.filter (fun i => i ≠ j),
        (if 1 ≤ n j then mu i * R i j * productForm (fun i m => rho i ^ m) N (moveState n i j)
          else 0) = productForm (fun i m => rho i ^ m) N n / rho j * (mu i * R i j * rho i) := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_filter.1 hi).2
      rw [if_pos hj, moveState_eq_mvC n i j hij]
      have h := pf_mvC rho n j i hn hj
      have hr := (hrho j).ne'
      field_simp
      linear_combination (mu i * R i j) * h
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.filter_ne' univ j,
      Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    have ht := htraffic j
    have hr := (hrho j).ne'
    have e : ∑ i, mu i * R i j * rho i = mu j * rho j := by
      rw [ht]
    rw [e]; field_simp
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun i _ => if_neg hj

lemma bal_lin {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (p q : (Fin k → ℕ) → ℝ)
    (c : ℝ) (n : Fin k → ℕ) (hp : BalanceAt mu R p n) (hq : BalanceAt mu R q n) :
    BalanceAt mu R (fun m => c * p m - q m) n := by
  unfold BalanceAt at *
  have hL : (∑ j, ∑ i ∈ univ.filter (fun i => i ≠ j),
      if 1 ≤ n j then mu i * R i j * (c * p (moveState n i j) - q (moveState n i j)) else 0) =
      c * (∑ j, ∑ i ∈ univ.filter (fun i => i ≠ j),
        if 1 ≤ n j then mu i * R i j * p (moveState n i j) else 0) -
      (∑ j, ∑ i ∈ univ.filter (fun i => i ≠ j),
        if 1 ≤ n j then mu i * R i j * q (moveState n i j) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hR : (∑ i, if 1 ≤ n i then mu i * (1 - R i i) * (c * p n - q n) else 0) =
      c * (∑ i, if 1 ≤ n i then mu i * (1 - R i i) * p n else 0) -
      (∑ i, if 1 ≤ n i then mu i * (1 - R i i) * q n else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hL, hR, hp, hq]

lemma zero_prop {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (hmu : ∀ i, 0 < mu i)
    (hR : IsRoutingMatrix R) (d : (Fin k → ℕ) → ℝ) (hd : ∀ m, 0 ≤ d m)
    (n : Fin k → ℕ) (hb : BalanceAt mu R d n) (hn0 : d n = 0) (i j : Fin k) (hj : 1 ≤ n j)
    (hij : i ≠ j) (hR' : 0 < R i j) : d (mvC n j i) = 0 := by
  unfold BalanceAt at hb
  have hR0 : (∑ i, if 1 ≤ n i then mu i * (1 - R i i) * d n else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [hn0]; simp)
  rw [hR0] at hb
  have hnn : ∀ j ∈ (univ : Finset (Fin k)), 0 ≤ ∑ i ∈ univ.filter (fun i => i ≠ j),
      (if 1 ≤ n j then mu i * R i j * d (moveState n i j) else 0) := by
    intro j _
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · exact mul_nonneg (mul_nonneg (hmu i).le (hR.1 i j)) (hd _)
    · exact le_rfl
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hb j (Finset.mem_univ j)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    rw [if_pos hj]
    exact mul_nonneg (mul_nonneg (hmu i).le (hR.1 i j)) (hd _))).1 h1 i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hij⟩)
  rw [if_pos hj, moveState_eq_mvC n i j hij] at h2
  have hpos : 0 < mu i * R i j := mul_pos (hmu i) hR'
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hpos.ne'
  · exact h

lemma reach_move {k : ℕ} (R : Fin k → Fin k → ℝ) (Z : Set (Fin k → ℕ))
    (hcl : ∀ n ∈ Z, ∀ i j, 1 ≤ n j → 0 < R i j → mvC n j i ∈ Z)
    (a b : Fin k) (h : Relation.ReflTransGen (fun x y => 0 < R x y) b a) :
    ∀ n ∈ Z, 1 ≤ n a → mvC n a b ∈ Z := by
  induction h with
  | refl => intro n hn _; rw [mvC_self]; exact hn
  | @tail c a' _ hca ih =>
    intro n hn ha
    have h1 : mvC n a' c ∈ Z := hcl n hn c a' ha hca
    have h2 : 1 ≤ mvC n a' c c := by
      simp only [mvC, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases hca' : c = a'
      · subst hca'; simp; omega
      · simp [hca']
    have := ih _ h1 h2
    rwa [mvC_mvC n a' b c ha] at this

lemma reach_all {k N : ℕ} (R : Fin k → Fin k → ℝ) (hirr : IsIrreducible R)
    (Z : Set (Fin k → ℕ)) (hZ : ∀ n ∈ Z, n ∈ states k N)
    (hcl : ∀ n ∈ Z, ∀ i j, 1 ≤ n j → 0 < R i j → mvC n j i ∈ Z) :
    ∀ D : ℕ, ∀ m ∈ Z, ∀ n ∈ states k N, ∑ x, (m x - n x) = D → n ∈ Z := by
  intro D
  induction D with
  | zero =>
    intro m hm n hn hD
    have hle : ∀ x ∈ (univ : Finset (Fin k)), m x ≤ n x := by
      intro x hx
      have := (Finset.sum_eq_zero_iff.1 hD) x hx; omega
    have hsm := (mem_states_iff m).1 (hZ m hm)
    have hsn := (mem_states_iff n).1 hn
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsm, hsn])
    have : m = n := funext fun x => heq x (Finset.mem_univ x)
    rw [← this]; exact hm
  | succ D ih =>
    intro m hm n hn hD
    obtain ⟨a, -, ha⟩ : ∃ a ∈ (univ : Finset (Fin k)), 0 < m a - n a := by
      by_contra hcon
      push_neg at hcon
      have : ∑ x, (m x - n x) = 0 := Finset.sum_eq_zero fun x hx => by
        have := hcon x hx; omega
      omega
    obtain ⟨b, hb⟩ : ∃ b, m b < n b := by
      by_contra hcon
      push_neg at hcon
      have hsm := (mem_states_iff m).1 (hZ m hm)
      have hsn := (mem_states_iff n).1 hn
      have hle : ∀ x ∈ (univ : Finset (Fin k)), n x ≤ m x := fun x _ => hcon x
      have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsm, hsn])
      have := heq a (Finset.mem_univ a); omega
    have ha1 : 1 ≤ m a := by omega
    have hm' : mvC m a b ∈ Z := reach_move R Z hcl a b (hirr b a) m hm ha1
    refine ih _ hm' n hn ?_
    have hpt : ∀ x, (mvC m a b x - n x) + (Pi.single a 1 : Fin k → ℕ) x = m x - n x := by
      intro x
      simp only [mvC, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases hxa : x = a
      · subst hxa
        have hab : x ≠ b := by rintro rfl; omega
        simp [hab]; omega
      · by_cases hxb : x = b
        · subst hxb; simp [hxa]; omega
        · simp [hxa, hxb]
    have := Finset.sum_congr rfl (fun x (_ : x ∈ (univ : Finset (Fin k))) => hpt x)
    rw [Finset.sum_add_distrib, Finset.sum_pi_single'] at this
    simp at this; omega

theorem closed_product_form_core {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) :
    IsClosedSteadyState mu R N p ↔ p = productForm (fun i n => rho i ^ n) N := by
  set π := productForm (fun i n => rho i ^ n) N with hπ
  have hG := normConst_pos rho hrho N
  have hπpos : ∀ n ∈ states k N, 0 < π n := by
    intro n hn; rw [hπ, productForm, if_pos hn]; exact div_pos (prod_pos' rho hrho n) hG
  have hπ0 : ∀ n, n ∉ states k N → π n = 0 := by
    intro n hn; rw [hπ, productForm, if_neg hn]
  have hπbal : ∀ n ∈ states k N, BalanceAt mu R π n := fun n hn =>
    pf_balance mu R rho hrho htraffic n hn
  have hπsum : ∑ n ∈ states k N, π n = 1 := pf_sum rho hrho N
  constructor
  · rintro ⟨hp0, hpz, hps, hpb⟩
    obtain ⟨n0, hn0, hmax⟩ := Finset.exists_max_image (states k N) (fun n => p n / π n)
      (states_nonempty N)
    set c := p n0 / π n0 with hc
    set d : (Fin k → ℕ) → ℝ := fun m => c * π m - p m with hd
    have hdnn : ∀ m, 0 ≤ d m := by
      intro m
      by_cases hm : m ∈ states k N
      · have h1 := hmax m hm
        have h2 := hπpos m hm
        rw [div_le_iff₀ h2] at h1
        simp only [hd]; linarith
      · simp only [hd]; rw [hπ0 m hm, hpz m hm]; simp
    have hdb : ∀ n ∈ states k N, BalanceAt mu R d n := fun n hn =>
      bal_lin mu R π p c n (hπbal n hn) (hpb n hn)
    have hdn0 : d n0 = 0 := by
      simp only [hd, hc]; field_simp [(hπpos n0 hn0).ne']; ring
    let Z : Set (Fin k → ℕ) := {m | m ∈ states k N ∧ d m = 0}
    have hcl : ∀ n ∈ Z, ∀ i j, 1 ≤ n j → 0 < R i j → mvC n j i ∈ Z := by
      rintro n ⟨hn, hdn⟩ i j hj hRij
      refine ⟨mvC_mem n j i hn hj, ?_⟩
      by_cases hij : i = j
      · subst hij; rw [mvC_self]; exact hdn
      · exact zero_prop mu R hmu hR d hdnn n (hdb n hn) hdn i j hj hij hRij
    have hall : ∀ n ∈ states k N, n ∈ Z := fun n hn =>
      reach_all R hirr Z (fun m hm => hm.1) hcl _ n0 ⟨hn0, hdn0⟩ n hn rfl
    have hpeq : ∀ m, p m = c * π m := by
      intro m
      by_cases hm : m ∈ states k N
      · have := (hall m hm).2; simp only [hd] at this; linarith
      · rw [hπ0 m hm, hpz m hm]; simp
    have hc1 : c = 1 := by
      have : ∑ n ∈ states k N, p n = c * ∑ n ∈ states k N, π n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => hpeq n
      rw [hps, hπsum] at this; linarith
    funext m; rw [hpeq m, hc1, one_mul]
  · rintro rfl
    refine ⟨fun n => ?_, hπ0, hπsum, hπbal⟩
    by_cases hn : n ∈ states k N
    · exact (hπpos n hn).le
    · rw [hπ0 n hn]

end QueueingFundamentals.Networks

open QueueingFundamentals.Networks


theorem solution {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) :
    IsClosedSteadyState mu R N p ↔ p = productForm (fun i n => rho i ^ n) N := by
  exact closed_product_form_core mu R rho hmu hR hirr hrho htraffic N p
