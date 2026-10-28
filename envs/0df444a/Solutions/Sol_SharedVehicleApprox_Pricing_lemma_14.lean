-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:23:25.144737+00:00
-- url     : https://prove2.me/submissions/7cd7081a-9e5d-40df-a521-ea1e64bfcdcd

import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Init
import Mathlib

section
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


theorem community_closed_product_form {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) :
    IsClosedSteadyState mu R N p ↔ p = productForm (fun i n => rho i ^ n) N := by
  exact closed_product_form_core mu R rho hmu hR hirr hrho htraffic N p

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem weighted_average_bounds {α : Type} (s : Finset α) (p q : α → ℝ)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hq : ∀ x ∈ s, 0 ≤ q x ∧ q x ≤ 1) :
    0 ≤ ∑ x ∈ s, p x * q x ∧ (∑ x ∈ s, p x * q x) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x hx => mul_nonneg (hp x hx) (hq x hx).1)
  · calc
      _ ≤ ∑ x ∈ s, p x := Finset.sum_le_sum (fun x hx => mul_le_of_le_one_right (hp x hx) (hq x hx).2)
      _ = 1 := hp1

theorem flow_bounds {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) (i j : Fin n) :
    0 ≤ flow n m φ q π i j ∧ flow n m φ q π i j ≤ φ i j := by
  have h := weighted_average_bounds (states n m) π (fun x => q x i j)
    (fun x _ => hπ.1 x) hπ.2.2.1 (fun x hx => ⟨(hq x hx i j).1,(hq x hx i j).2.1⟩)
  have he : flow n m φ q π i j = φ i j * ∑ x ∈ states n m, π x * q x i j := by
    simp only [flow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  exact ⟨mul_nonneg (hφ i j) h.1, mul_le_of_le_one_right (hφ i j) h.2⟩

theorem infinite_circulation {n : ℕ} [NeZero n] (φ q : Fin n → Fin n → ℝ)
    (r : Fin n → ℝ) (htr : IsTraffic φ q r) (i : Fin n) :
    ∑ k, availInf r k * φ k i * q k i = ∑ j, availInf r i * φ i j * q i j := by
  simp only [availInf,div_mul_eq_mul_div,← Finset.sum_div]
  rw [htr i,Finset.mul_sum]
  simp only [mul_assoc]

end Queelius.SharedVehicle

open Queelius.SharedVehicle SharedVehicleApprox.Pricing

theorem shared_vehicle_demand_bound {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) (i j : Fin n) :
    flow n m φ q π i j ≤ φ i j :=
  (flow_bounds φ hφ q π hq hπ i j).2

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem mvC_destination {n : ℕ} (x : Fin n → ℕ) (i j : Fin n) (hx : 1 ≤ x i) :
    1 ≤ mvC x i j j := by
  by_cases hij : i=j
  · subst j
    simpa only [mvC_self] using hx
  · simp [mvC,Pi.single_apply,hij,Ne.symm hij]

theorem mvC_inverse {n : ℕ} (x : Fin n → ℕ) (i j : Fin n) (hx : 1 ≤ x i) :
    mvC (mvC x i j) j i = x := by
  rw [mvC_mvC x i i j hx,mvC_self]

theorem occupied_move_sum {n m : ℕ} (i j : Fin n) (F : (Fin n → ℕ) → ℝ) :
    (∑ x ∈ (states n m).filter (fun x => 1 ≤ x j), F (mvC x j i)) =
    ∑ y ∈ (states n m).filter (fun y => 1 ≤ y i), F y := by
  refine Finset.sum_bij (fun x hx => mvC x j i) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨mvC_mem x j i hx hj,mvC_destination x j i hj⟩
  · intro x hx y hy he
    have h := congrArg (fun z => mvC z i j) he
    simpa only [mvC_inverse x j i (Finset.mem_filter.mp hx).2,
      mvC_inverse y j i (Finset.mem_filter.mp hy).2] using h
  · intro y hy
    obtain ⟨hy,hi⟩ := Finset.mem_filter.mp hy
    exact ⟨mvC y i j,Finset.mem_filter.mpr ⟨mvC_mem y i j hy hi,mvC_destination y i j hi⟩,
      mvC_inverse y i j hi⟩
  · intro x hx
    rfl

theorem weighted_inflow_transport {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π g : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (i j : Fin n) :
    (∑ x ∈ states n m, g x * inflowTerm φ q π x i j) =
    ∑ x ∈ states n m, g (mvC x i j) * (π x * φ i j * q x i j) := by
  by_cases hij : i=j
  · subst j
    simp [inflowTerm,mvC_self]
  · have he := occupied_move_sum (m:=m) i j
      (fun y => g (mvC y i j) * (π y * φ i j * q y i j))
    have hleft : (∑ x ∈ states n m, g x * inflowTerm φ q π x i j) =
        ∑ x ∈ (states n m).filter (fun x => 1 ≤ x j),
          g (mvC (mvC x j i) i j) * (π (mvC x j i) * φ i j * q (mvC x j i) i j) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hj : 1 ≤ x j
      · simp [inflowTerm,hij,hj,moveState_eq_mvC x i j hij,mvC_inverse x j i hj]
      · simp [inflowTerm,hij,hj]
    rw [hleft,he,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hi : 1 ≤ x i
    · simp [hi]
    · have h0 : x i = 0 := by omega
      simp [hi,(hq x hx i j).2.2 h0]

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem finite_sum_rotate {α β γ : Type} (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → ℝ) :
    (∑ x ∈ s, ∑ i ∈ t, ∑ j ∈ u, f x i j) = ∑ i ∈ t, ∑ j ∈ u, ∑ x ∈ s, f x i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

theorem stationary_weighted_balance {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π g : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    (∑ i, ∑ j, ∑ x ∈ states n m, g x * (π x * φ i j * q x i j)) =
      ∑ i, ∑ j, ∑ x ∈ states n m, g (mvC x i j) * (π x * φ i j * q x i j) := by
  have hb : (∑ x ∈ states n m, g x * (π x * (∑ i, ∑ j, φ i j * q x i j))) =
      ∑ x ∈ states n m, g x * (∑ i, ∑ j, inflowTerm φ q π x i j) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hπ.2.2.2 x hx]
  simp only [Finset.mul_sum] at hb
  rw [finite_sum_rotate (states n m) univ univ,finite_sum_rotate (states n m) univ univ] at hb
  have ht : (∑ i, ∑ j, ∑ x ∈ states n m, g x * inflowTerm φ q π x i j) =
      ∑ i, ∑ j, ∑ x ∈ states n m, g (mvC x i j) * (π x * φ i j * q x i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact weighted_inflow_transport φ q π g hq i j
  simpa only [mul_assoc] using hb.trans ht

theorem mvC_coordinate_delta {n : ℕ} (x : Fin n → ℕ) (i j k : Fin n) (hi : 1 ≤ x i) :
    ((mvC x i j k : ℕ) : ℝ) - (x k : ℝ) =
      (if k=j then 1 else 0 : ℝ) - (if k=i then 1 else 0) := by
  have h := congrFun (mvC_add x i j hi) k
  simp only [Pi.add_apply,Pi.single_apply] at h
  split_ifs at h ⊢ <;> have hh := congrArg (fun t : ℕ => (t : ℝ)) h <;>
    push_cast at hh <;> linarith

theorem stationary_circulation {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) (k : Fin n) :
    ∑ i, flow n m φ q π i k = ∑ j, flow n m φ q π k j := by
  have hb := stationary_weighted_balance φ q π (fun x => (x k : ℝ)) hq hπ
  have hd (i j : Fin n) (x : Fin n → ℕ) (hx : x ∈ states n m) :
      (mvC x i j k : ℝ) * (π x * φ i j * q x i j) - (x k : ℝ) * (π x * φ i j * q x i j) =
      (if k=j then π x * φ i j * q x i j else 0) -
      (if k=i then π x * φ i j * q x i j else 0) := by
    by_cases hi : 1 ≤ x i
    · rw [← sub_mul,mvC_coordinate_delta x i j k hi,sub_mul]
      simp only [ite_mul,one_mul,zero_mul]
    · have hz : q x i j = 0 := (hq x hx i j).2.2 (by omega)
      simp [hz]
  have hz : (∑ i, ∑ j, ∑ x ∈ states n m,
      ((if k=j then π x * φ i j * q x i j else 0) -
      (if k=i then π x * φ i j * q x i j else 0))) = 0 := by
    calc
      _ = ∑ i, ∑ j, ∑ x ∈ states n m,
          ((mvC x i j k : ℝ) * (π x * φ i j * q x i j) -
          (x k : ℝ) * (π x * φ i j * q x i j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_congr rfl (fun x hx => (hd i j x hx).symm)
      _ = 0 := by simp only [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr hb.symm
  simp only [Finset.sum_sub_distrib] at hz
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero] at hz
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,flow] at hz ⊢
  exact sub_eq_zero.mp hz

theorem supply_circulation {n m : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) :
    (∀ (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ),
      IsPolicy n m q → IsStationary n m φ q π →
        ∀ i, ∑ k, flow n m φ q π k i = ∑ j, flow n m φ q π i j) ∧
    (∀ (q : Fin n → Fin n → ℝ) (r : Fin n → ℝ),
      (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) → (∀ i, 0 ≤ r i) → (∃ j, 0 < r j) → IsTraffic φ q r →
        ∀ i, ∑ k, availInf r k * φ k i * q k i = ∑ j, availInf r i * φ i j * q i j) := by
  constructor
  · intro q π hq hπ i
    exact stationary_circulation φ q π hq hπ i
  · intro q r hq hr hp htr i
    exact infinite_circulation φ q r htr i

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

def averagePolicy {n m : ℕ} (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) (i j : Fin n) : ℝ := ∑ x ∈ states n m, π x * q x i j

theorem flow_as_average {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ) (i j : Fin n) :
    flow n m φ q π i j = φ i j * averagePolicy (m:=m) q π i j := by
  simp only [flow,averagePolicy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem average_policy_feasible {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    IsRelaxFeasible φ (averagePolicy (m:=m) q π) := by
  constructor
  · intro i j
    exact weighted_average_bounds _ _ _ (fun x _ => hπ.1 x) hπ.2.2.1
      (fun x hx => ⟨(hq x hx i j).1,(hq x hx i j).2.1⟩)
  · intro i
    simpa only [flow_as_average] using stationary_circulation φ q π hq hπ i

theorem average_objective_upper_bound {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    obj n m φ I q π ≤ elevObj φ I (averagePolicy (m:=m) q π) := by
  have hj (i j : Fin n) : (∑ x ∈ states n m, π x * rewardCurve I i j (q x i j)) ≤
      rewardCurve I i j (averagePolicy (m:=m) q π i j) := by
    simpa only [smul_eq_mul,averagePolicy] using (hR i j).le_map_sum
      (fun x _ => hπ.1 x) hπ.2.2.1
      (fun x hx => ⟨(hq x hx i j).1,(hq x hx i j).2.1⟩)
  unfold obj elevObj
  simp only [Finset.mul_sum]
  rw [finite_sum_rotate]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj'
  calc
    _ = φ i j * ∑ x ∈ states n m, π x * rewardCurve I i j (q x i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hj i j) (hφ i j)

theorem relaxation_optimum_upper_bound {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (qt : Fin n → Fin n → ℝ) (hopt : IsRelaxOptimal φ I qt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    obj n m φ I q π ≤ elevObj φ I qt :=
  (average_objective_upper_bound φ hφ I hR q π hq hπ).trans
    (hopt.2 _ (average_policy_feasible φ q π hq hπ))

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

def removeUnit {n : ℕ} (x : Fin n → ℕ) (i : Fin n) : Fin n → ℕ := x - Pi.single i 1

theorem removeUnit_add {n : ℕ} (x : Fin n → ℕ) (i : Fin n) (hi : 1 ≤ x i) :
    removeUnit x i + Pi.single i 1 = x := by
  ext j
  simp only [removeUnit,Pi.sub_apply,Pi.add_apply,Pi.single_apply]
  split_ifs <;> subst_vars <;> omega

theorem removeUnit_mem {n m : ℕ} (hm : 1 ≤ m) (x : Fin n → ℕ) (i : Fin n)
    (hx : x ∈ states n m) (hi : 1 ≤ x i) : removeUnit x i ∈ states n (m-1) := by
  have h := congrArg (fun y : Fin n → ℕ => ∑ j, y j) (removeUnit_add x i hi)
  rw [sum_add_single,(mem_states_iff x).mp hx] at h
  rw [mem_states_iff]
  omega

theorem add_unit_sum {n m : ℕ} (hm : 1 ≤ m) (i : Fin n) (F : (Fin n → ℕ) → ℝ) :
    (∑ x ∈ (states n m).filter (fun x => 1 ≤ x i), F x) =
      ∑ y ∈ states n (m-1), F (y + Pi.single i 1) := by
  symm
  refine Finset.sum_bij (fun y hy => y + Pi.single i 1) ?_ ?_ ?_ ?_
  · intro y hy
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [Nat.sub_add_cancel hm] using add_single_mem y i hy
    · simp
  · intro x hx y hy he
    exact add_right_cancel he
  · intro x hx
    obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
    exact ⟨removeUnit x i,removeUnit_mem hm x i hx hi,removeUnit_add x i hi⟩
  · intro y hy
    rfl

theorem product_weight_add_unit {n : ℕ} (ρ : Fin n → ℕ → ℝ) (i : Fin n) (r : ℝ)
    (hρ : ∀ y, ρ i y = r^y) (y : Fin n → ℕ) :
    (∏ j, ρ j ((y + Pi.single i 1 : Fin n → ℕ) j)) = (∏ j, ρ j (y j)) * r := by
  have hterm (j : Fin n) : ρ j ((y + Pi.single i 1 : Fin n → ℕ) j) =
      ρ j (y j) * (if j=i then r else 1) := by
    by_cases hji : j=i
    · subst j
      simp [hρ,pow_succ]
    · simp [Pi.single_apply,hji]
  simp_rw [hterm,Finset.prod_mul_distrib]
  simp

theorem product_form_availability {n m : ℕ} (hm : 1 ≤ m) (ρ : Fin n → ℕ → ℝ)
    (i : Fin n) (r : ℝ) (hρ : ∀ y, ρ i y = r^y) :
    availability m (productForm ρ m) i = normConst ρ (m-1) / normConst ρ m * r := by
  unfold availability tailMarginal
  rw [add_unit_sum hm]
  have hmem (y : Fin n → ℕ) (hy : y ∈ states n (m-1)) :
      y + Pi.single i 1 ∈ states n m := by
    simpa only [Nat.sub_add_cancel hm] using add_single_mem y i hy
  calc
    _ = ∑ y ∈ states n (m-1), ((∏ j, ρ j (y j)) * r) / normConst ρ m := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [productForm,if_pos (hmem y hy),product_weight_add_unit ρ i r hρ]
    _ = _ := by simp only [← Finset.sum_div,← Finset.sum_mul,normConst]; ring

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem objective_by_availability {n m : ℕ} (φ : Fin n → Fin n → ℝ)
    (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) :
    obj n m φ I (toPolicy q) π =
      ∑ i, availability m π i * ∑ j, φ i j * rewardCurve I i j (q i j) := by
  unfold obj
  simp only [Finset.mul_sum]
  rw [finite_sum_rotate]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum,availability,tailMarginal,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : 0 < x i
  · simp [toPolicy,h,show 1 ≤ x i from h]
  · simp [toPolicy,h,show ¬1 ≤ x i from h,rewardCurve]

theorem G_nonnegative {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (m : ℕ) : 0 ≤ G r m :=
  Finset.sum_nonneg (fun x hx => Finset.prod_nonneg (fun i hi => pow_nonneg (hr i) _))

theorem rmax_positive {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hp : ∃ i, 0 < r i) : 0 < rmax r := by
  obtain ⟨i,hi⟩ := hp
  exact hi.trans_le (Finset.le_sup' r (Finset.mem_univ i))

theorem power_availability {n m : ℕ} (hm : 1 ≤ m) (r : Fin n → ℝ) (i : Fin n) :
    availability m (productForm (fun j y => r j ^ y) m) i = G r (m-1) / G r m * r i :=
  product_form_availability hm (fun j y => r j ^ y) i (r i) (fun _ => rfl)

theorem product_objective_scale {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (hp : ∃ i, 0 < r i) :
    obj n m φ I (toPolicy q) (productForm (fun j y => r j ^ y) m) =
      (rmax r * G r (m-1) / G r m) * objInf φ I q r := by
  rw [objective_by_availability]
  simp_rw [power_availability hm]
  unfold objInf availInf G
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [(rmax_positive r hp).ne']

theorem product_max_availability {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    univ.sup' univ_nonempty (fun i => availability m (productForm (fun j y => r j ^ y) m) i) =
      rmax r * G r (m-1) / G r m := by
  have hg : 0 ≤ G r (m-1) / G r m := div_nonneg (G_nonnegative r hr _) (G_nonnegative r hr _)
  simp_rw [power_availability hm]
  change univ.sup' univ_nonempty (fun i => G r (m-1) / G r m * r i) = _
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    calc
      _ ≤ G r (m-1) / G r m * rmax r := mul_le_mul_of_nonneg_left (Finset.le_sup' r hi) hg
      _ = _ := by ring
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty r
    have h := Finset.le_sup' (fun i => G r (m-1) / G r m * r i) hi
    change rmax r = r i at he
    rw [← he] at h
    convert h using 1 <;> ring

theorem finite_infinite_objective {n m : ℕ} [NeZero n] (hm : 1 ≤ m) (φ : Fin n → Fin n → ℝ)
    (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (hp : ∃ j, 0 < r j) :
    obj n m φ I (toPolicy q) (productForm (fun j y => r j ^ y) m) =
        (rmax r * G r (m-1) / G r m) * objInf φ I q r ∧
      univ.sup' univ_nonempty (fun i => availability m (productForm (fun j y => r j ^ y) m) i) =
        rmax r * G r (m-1) / G r m :=
  ⟨product_objective_scale hm φ I q r hp,product_max_availability hm r hr⟩

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

def removalWeight {n : ℕ} (m : ℕ) (x y : Fin n → ℕ) : ℝ :=
  ∑ i, if x=y+Pi.single i 1 then (x i : ℝ)/m else 0

theorem removalWeight_nonnegative {n m : ℕ} (x y : Fin n → ℕ) : 0 ≤ removalWeight m x y := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · positivity
  · rfl

theorem removalWeight_support {n m : ℕ} (x y : Fin n → ℕ)
    (h : removalWeight m x y ≠ 0) : ∃ i, x=y+Pi.single i 1 := by
  by_contra hn
  apply h
  unfold removalWeight
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (fun he => hn ⟨i,he⟩)

theorem adjacent_remove_iff {n : ℕ} (x y : Fin n → ℕ) (i : Fin n) (hi : 1 ≤ x i) :
    x=y+Pi.single i 1 ↔ y=removeUnit x i := by
  constructor
  · intro h
    apply add_right_cancel (b := Pi.single i 1)
    rw [← h,removeUnit_add x i hi]
  · intro h
    rw [h,removeUnit_add x i hi]

theorem removalWeight_row {n m : ℕ} (hm : 1 ≤ m) (x : Fin n → ℕ) (hx : x ∈ states n m) :
    (∑ y ∈ states n (m-1), removalWeight m x y)=1 := by
  unfold removalWeight
  rw [Finset.sum_comm]
  have hterm (i : Fin n) :
      (∑ y ∈ states n (m-1), if x=y+Pi.single i 1 then (x i : ℝ)/m else 0) = (x i : ℝ)/m := by
    by_cases hi : 1 ≤ x i
    · simp only [adjacent_remove_iff x _ i hi]
      simp [removeUnit_mem hm x i hx hi]
    · have hz : x i=0 := by omega
      simp [hz]
  simp_rw [hterm]
  rw [← Finset.sum_div,← Nat.cast_sum,(mem_states_iff x).mp hx]
  exact div_self (by exact_mod_cast (show m ≠ 0 by omega))

theorem removalWeight_column {n m : ℕ} (hm : 1 ≤ m) (y : Fin n → ℕ)
    (hy : y ∈ states n (m-1)) :
    (∑ x ∈ states n m, removalWeight m x y)=((m:ℝ)+n-1)/m := by
  unfold removalWeight
  rw [Finset.sum_comm]
  have hterm (i : Fin n) :
      (∑ x ∈ states n m, if x=y+Pi.single i 1 then (x i : ℝ)/m else 0) = ((y i : ℝ)+1)/m := by
    have hi : y+Pi.single i 1 ∈ states n m := by
      simpa only [Nat.sub_add_cancel hm] using add_single_mem y i hy
    simp [hi]
  simp_rw [hterm]
  rw [← Finset.sum_div,Finset.sum_add_distrib,← Nat.cast_sum,(mem_states_iff y).mp hy]
  simp [Nat.cast_sub hm]
  congr 1
  ring

theorem lattice_weights {n m : ℕ} (hm : 1 ≤ m) :
    ∃ ω : (Fin n → ℕ) → (Fin n → ℕ) → ℝ,
      (∀ x y, 0 ≤ ω x y) ∧
      (∀ x ∈ states n m, ∀ y ∈ states n (m-1), ω x y ≠ 0 → ∃ i, x=y+Pi.single i 1) ∧
      (∀ y ∈ states n (m-1), ∑ x ∈ states n m, ω x y = ((m:ℝ)+n-1)/m) ∧
      (∀ x ∈ states n m, ∑ y ∈ states n (m-1), ω x y = 1) :=
  ⟨removalWeight m,removalWeight_nonnegative,
    fun x _ y _ h => removalWeight_support x y h,removalWeight_column hm,removalWeight_row hm⟩

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem balanced_harmonic_constant {n : ℕ} [NeZero n] (w : Fin n → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hb : ∀ i, ∑ k, w k i = ∑ j, w i j)
    (hc : ∀ i j, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < w a b) i j)
    (A : Fin n → ℝ) (ha : ∀ i, ∑ k, A k * w k i = A i * ∑ j, w i j) :
    ∀ i j, A i = A j := by
  let M := univ.sup' univ_nonempty A
  obtain ⟨z,hz,hMz⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty A
  have hle (i : Fin n) : A i ≤ M := Finset.le_sup' A (Finset.mem_univ i)
  have back (i j : Fin n) (hij : 0 < w i j) (hj : A j = M) : A i = M := by
    have hs : (∑ k, (M-A k)*w k j) = 0 := by
      simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
      rw [hb j,ha j,hj,sub_self]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (sub_nonneg.mpr (hle k)) (hw k j))).mp hs i (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right (ne_of_gt hij))).symm
  have hall (i : Fin n) : A i = M := by
    have path := hc i z
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact hMz.symm
    | @head a b hab hpath ih => exact back a b hab.2 ih
  intro i j
  exact (hall i).trans (hall j).symm

theorem flow_state_independent {n m : ℕ} (φ q : Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) (i j : Fin n) :
    flow n m φ (toPolicy q) π i j = availability m π i * φ i j * q i j := by
  simp only [flow,availability,tailMarginal,Finset.sum_filter,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : 0 < x i
  · simp [toPolicy,hi,show 1 ≤ x i from hi]
  · simp [toPolicy,hi,show ¬1 ≤ x i from hi]

theorem state_independent_policy {n m : ℕ} (q : Fin n → Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) : IsPolicy n m (toPolicy q) := by
  intro x hx i j
  by_cases hi : 0 < x i
  · simp [toPolicy,hi,hq i j,show x i ≠ 0 from Nat.ne_of_gt hi]
  · simp [toPolicy,hi]

theorem balanced_equal_availabilities {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (q : Fin n → Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) (hb : IsBalanced φ q) (hc : SupportConnected φ q) :
    (∀ (m : ℕ) (π : (Fin n → ℕ) → ℝ), IsStationary n m φ (toPolicy q) π →
      ∀ i j, availability m π i = availability m π j) ∧
    (∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
      ∀ i j, availInf r i = availInf r j) := by
  constructor
  · intro m π hπ
    apply balanced_harmonic_constant (fun i j => φ i j * q i j)
      (fun i j => mul_nonneg (hφ i j) (hq i j).1) hb hc
    intro i
    have h := stationary_circulation φ (toPolicy q) π (state_independent_policy q hq) hπ i
    simpa only [flow_state_independent,Finset.mul_sum,mul_assoc] using h
  · intro r hr ht
    have he := balanced_harmonic_constant (fun i j => φ i j * q i j)
      (fun i j => mul_nonneg (hφ i j) (hq i j).1) hb hc r
      (by intro i; simpa only [mul_assoc] using ht i)
    intro i j
    unfold availInf
    rw [he i j]

theorem balanced_infinite_objective {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) (hb : IsBalanced φ q) (hc : SupportConnected φ q)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (ht : IsTraffic φ q r) :
    objInf φ I q r = elevObj φ I q := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty r
  have heq := (balanced_equal_availabilities φ hφ q hq hb hc).2 r hr ht
  have hz : availInf r j = 1 := by
    change r j / rmax r = 1
    change rmax r = r j at he
    rw [he,div_self (ne_of_gt (hr j))]
  unfold objInf elevObj
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq i j,hz,one_mul]

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem G_positive_some {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hp : ∃ j, 0 < r j) (m : ℕ) : 0 < G r m := by
  obtain ⟨i,hi⟩ := hp
  have hx : Pi.single i m ∈ states n m := by rw [mem_states_iff]; simp
  have he : (∏ j, r j ^ (Pi.single i m j)) = r i ^ m := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [Pi.single_apply,hji]
    · simp
  have ht : 0 < ∏ j, r j ^ (Pi.single i m j) := by rw [he]; exact pow_pos hi _
  apply ht.trans_le
  change (∏ j, r j ^ Pi.single i m j) ≤ ∑ x ∈ states n m, ∏ j, r j ^ x j
  exact Finset.single_le_sum (f := fun x : Fin n → ℕ => ∏ j, r j ^ x j) (fun x _ => Finset.prod_nonneg (fun j _ => pow_nonneg (hr j) _)) hx

theorem adjacent_product_bound {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (x y : Fin n → ℕ) (h : ∃ i, x=y+Pi.single i 1) :
    (∏ j, r j ^ x j) ≤ rmax r * ∏ j, r j ^ y j := by
  obtain ⟨i,rfl⟩ := h
  rw [prod_add_single]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Finset.le_sup' r (Finset.mem_univ i))
    (Finset.prod_nonneg (fun j _ => pow_nonneg (hr j) _))

theorem normalization_layer_bound {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    G r m ≤ (((m:ℝ)+n-1)/m) * rmax r * G r (m-1) := by
  calc
    G r m = ∑ x ∈ states n m, ∑ y ∈ states n (m-1),
        removalWeight m x y * ∏ j, r j ^ x j := by
      change (∑ x ∈ states n m, ∏ j, r j ^ x j) = _
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_mul,removalWeight_row hm x hx,one_mul]
    _ ≤ ∑ x ∈ states n m, ∑ y ∈ states n (m-1),
        removalWeight m x y * (rmax r * ∏ j, r j ^ y j) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hz : removalWeight m x y=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (adjacent_product_bound r hr x y (removalWeight_support x y hz))
          (removalWeight_nonnegative x y)
    _ = (((m:ℝ)+n-1)/m) * rmax r * G r (m-1) := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ y ∈ states n (m-1), (((m:ℝ)+n-1)/m) * (rmax r * ∏ j, r j ^ y j) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.sum_mul,removalWeight_column hm y hy]
        _ = _ := by simp only [← mul_assoc,← Finset.mul_sum,G,normConst]

theorem availability_lower_bound {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (hp : ∃ j, 0 < r j) :
    (m:ℝ)/((m:ℝ)+n-1) ≤ rmax r * G r (m-1) / G r m := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 1 ≤ (n:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hd : 0 < (m:ℝ)+n-1 := by linarith
  have hg := G_positive_some r hr hp m
  have hb := normalization_layer_bound hm r hr
  have hb' : G r m ≤ (((m:ℝ)+n-1) * (rmax r * G r (m-1))) / m := by
    convert hb using 1 <;> ring
  have hh := (le_div_iff₀ hm0).mp hb'
  apply (div_le_div_iff₀ hd hg).2
  nlinarith

theorem product_max_availability_bound {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (hp : ∃ j, 0 < r j) :
    univ.sup' univ_nonempty (fun i => availability m (productForm (fun j y => r j ^ y) m) i) =
        rmax r * G r (m-1) / G r m ∧
      (m:ℝ)/((m:ℝ)+n-1) ≤ rmax r * G r (m-1) / G r m :=
  ⟨product_max_availability hm r hr,availability_lower_bound hm r hr hp⟩

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle.Controls
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

def rates : Fin 2 → Fin 2 → ℝ := fun i j => if i=j then 0 else if i=0 then 2 else 1
def quantiles : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
def law (x : Fin 2 → ℕ) : ℝ := if x = ![1,0] then 1/3 else if x = ![0,1] then 2/3 else 0

theorem two_states : states 2 1 = {![1,0],![0,1]} := by decide

theorem example_policy : IsPolicy 2 1 (toPolicy quantiles) := by
  intro x hx i j
  by_cases hi : 0 < x i
  · simp [toPolicy,hi,quantiles,show x i ≠ 0 from Nat.ne_of_gt hi]
  · simp [toPolicy,hi]

theorem example_stationary : IsStationary 2 1 rates (toPolicy quantiles) law := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    unfold law
    split_ifs <;> norm_num
  · intro x hx
    have h0 : x ≠ ![1,0] := by intro h; subst x; simp [two_states] at hx
    have h1 : x ≠ ![0,1] := by intro h; subst x; simp [two_states] at hx
    simp [law,h0,h1]
  · norm_num [two_states,law]
  · intro x hx
    simp only [two_states,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      norm_num [rates,quantiles,law,toPolicy,inflowTerm,moveState,Fin.sum_univ_two,
        Function.update_apply,funext_iff,Fin.forall_fin_two]

theorem asymmetric_cycle_flows :
    flow 2 1 rates (toPolicy quantiles) law 0 1 = 2/3 ∧
    flow 2 1 rates (toPolicy quantiles) law 1 0 = 2/3 := by
  norm_num [flow,two_states,rates,toPolicy,quantiles,law]

theorem unavailability_control :
    availability 1 law 0 = 1/3 ∧ availability 1 law 1 = 2/3 := by
  norm_num [availability,tailMarginal,two_states,Finset.sum_filter,law]

theorem normalization_necessary_control :
    (∑ x ∈ ({0} : Finset ℕ), (2:ℝ) * (1:ℝ)) > 1 := by norm_num

theorem zero_mass_division_control :
    availability 1 (productForm (fun (_ : Fin 1) (y : ℕ) => (0:ℝ)^y) 1) 0 = 0 := by
  rw [power_availability (by norm_num)]
  simp

theorem disconnected_harmonic_control :
    (∀ i : Fin 2, (∑ k : Fin 2, (k.val : ℝ) * (0:ℝ)) = (i.val : ℝ) * ∑ _ : Fin 2, (0:ℝ)) ∧
      (0:ℝ) ≠ (1:ℝ) := by
  norm_num

end Queelius.SharedVehicle.Controls

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

def departureRate {n : ℕ} (φ q : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := ∑ j, φ i j*q i j

def routing {n : ℕ} (φ q : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  φ i j*q i j / departureRate φ q i

theorem routing_rate {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (hmu : ∀ i, 0 < departureRate φ q i) (i j : Fin n) :
    departureRate φ q i * routing φ q i j = φ i j*q i j := by
  unfold routing
  field_simp [(hmu i).ne']

theorem routing_normalized {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hq : ∀ i j, 0 ≤ q i j)
    (hmu : ∀ i, 0 < departureRate φ q i) : IsRoutingMatrix (routing φ q) := by
  constructor
  · intro i j
    exact div_nonneg (mul_nonneg (hφ i j) (hq i j)) (hmu i).le
  · intro i
    simp only [routing,← Finset.sum_div]
    exact div_self (hmu i).ne'

theorem routing_traffic {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (hmu : ∀ i, 0 < departureRate φ q i) (r : Fin n → ℝ) :
    IsTraffic φ q r ↔ IsTrafficSolution (departureRate φ q) (routing φ q) r := by
  unfold IsTraffic IsTrafficSolution
  simp_rw [routing_rate φ q hmu]
  constructor <;> intro h i <;> have hi := h i
  · simpa only [departureRate,mul_comm,mul_left_comm,mul_assoc] using hi.symm
  · simpa only [departureRate,mul_comm,mul_left_comm,mul_assoc] using hi.symm

theorem routing_connected {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (hmu : ∀ i, 0 < departureRate φ q i) :
    SupportConnected φ q ↔ IsIrreducible (routing φ q) := by
  have he (i j : Fin n) : 0 < routing φ q i j ↔ 0 < φ i j*q i j :=
    div_pos_iff_of_pos_right (hmu i)
  constructor
  · intro h i j
    induction h i j with
    | refl => exact .refl
    | @tail b c hbc hstep ih => exact ih.tail ((he _ _).2 hstep.2)
  · intro h i j
    induction h i j with
    | refl => exact .refl
    | @tail b c hbc hstep ih =>
      by_cases h : b=c
      · subst c; exact ih
      · exact ih.tail ⟨h,(he _ _).1 hstep⟩

theorem inflow_independent_off_diagonal {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) (x : Fin n → ℕ) (i j : Fin n) (hij : i≠j) :
    inflowTerm φ (toPolicy q) π x i j =
      if 1 ≤ x j then φ i j*q i j*π (moveState x i j) else 0 := by
  by_cases hj : 1 ≤ x j
  · simp [inflowTerm,hij,hj,toPolicy,moveState,Function.update_self]
    ring
  · simp [inflowTerm,hij,hj]

theorem independent_balance_equivalence {n : ℕ} (φ q : Fin n → Fin n → ℝ)
    (hmu : ∀ i, 0 < departureRate φ q i)
    (π : (Fin n → ℕ) → ℝ) (x : Fin n → ℕ) :
    (π x * (∑ i, ∑ j, φ i j * toPolicy q x i j) =
      ∑ i, ∑ j, inflowTerm φ (toPolicy q) π x i j) ↔
    BalanceAt (departureRate φ q) (routing φ q) π x := by
  let D : ℝ := ∑ i, if 1 ≤ x i then φ i i*q i i*π x else 0
  let O : ℝ := ∑ i, if 1 ≤ x i then departureRate φ q i*π x else 0
  let B : ℝ := ∑ j, ∑ i ∈ univ.filter (fun i => i≠j),
    if 1 ≤ x j then φ i j*q i j*π (moveState x i j) else 0
  have hout : π x*(∑ i, ∑ j, φ i j*toPolicy q x i j)=O := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : 1 ≤ x i
    · simp [toPolicy,show 0<x i from hx,hx,departureRate,O,mul_comm]
    · simp [toPolicy,show ¬0<x i from hx,hx,O]
  have hin : (∑ i, ∑ j, inflowTerm φ (toPolicy q) π x i j)=B+D := by
    rw [Finset.sum_comm]
    change _ = (∑ j, ∑ i ∈ univ.filter (fun i => i≠j),
      if 1 ≤ x j then φ i j*q i j*π (moveState x i j) else 0) +
      ∑ j, if 1 ≤ x j then φ j j*q j j*π x else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_filter]
    have term (i : Fin n) : inflowTerm φ (toPolicy q) π x i j =
        (if i≠j then (if 1 ≤ x j then φ i j*q i j*π (moveState x i j) else 0) else 0) +
        (if i=j then (if 1 ≤ x j then φ j j*q j j*π x else 0) else 0) := by
      by_cases hij : i=j
      · subst i
        by_cases hx : 1 ≤ x j
        · simp [inflowTerm,toPolicy,show 0 < x j from hx,hx]; ring
        · simp [inflowTerm,toPolicy,show ¬0 < x j from hx,hx]
      · rw [inflow_independent_off_diagonal φ q π x i j hij]
        simp [hij]
    simp_rw [term,Finset.sum_add_distrib]
    simp
  have hright : (∑ i, if 1 ≤ x i then
      departureRate φ q i*(1-routing φ q i i)*π x else 0)=O-D := by
    change _ = (∑ i, if 1 ≤ x i then departureRate φ q i*π x else 0) -
      ∑ i, if 1 ≤ x i then φ i i*q i i*π x else 0
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : 1 ≤ x i
    · simp only [hx,ite_true,mul_sub,mul_one,routing_rate φ q hmu,sub_mul]
    · simp [hx]
  have hleft : (∑ j, ∑ i ∈ univ.filter (fun i => i≠j),
      if 1 ≤ x j then departureRate φ q i * routing φ q i j * π (moveState x i j) else 0)=B := by
    simp only [routing_rate φ q hmu,B]
  rw [hout,hin]
  unfold BalanceAt
  rw [hleft,hright]
  constructor <;> intro h <;> linarith

theorem gordon_newell_model {n : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hmu : ∀ i, 0 < ∑ j, φ i j*q i j) :
    let mu : Fin n → ℝ := fun i => ∑ j, φ i j*q i j
    let P : Fin n → Fin n → ℝ := fun i j => φ i j*q i j / mu i
    IsRoutingMatrix P ∧
      (∀ (m : ℕ) (π : (Fin n → ℕ) → ℝ),
        IsStationary n m φ (toPolicy q) π ↔ IsClosedSteadyState mu P m π) ∧
      (∀ r : Fin n → ℝ, IsTraffic φ q r ↔ IsTrafficSolution mu P r) ∧
      (SupportConnected φ q ↔ IsIrreducible P) := by
  change IsRoutingMatrix (routing φ q) ∧ _
  refine ⟨routing_normalized φ q hφ (fun i j => (hq i j).1) hmu,?_,routing_traffic φ q hmu,routing_connected φ q hmu⟩
  intro m π
  unfold SharedVehicleApprox.Pricing.IsStationary IsClosedSteadyState
  simp only [independent_balance_equivalence φ q hmu]
  rfl

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem states_one (m : ℕ) : states 1 m = {fun _ : Fin 1 => m} := by
  ext x
  rw [mem_states_iff,Finset.mem_singleton]
  simp only [Fin.sum_univ_one]
  constructor
  · intro h; ext i; fin_cases i; exact h
  · intro h; rw [h]

theorem connected_positive_departures {n : ℕ} (hn : 2 ≤ n)
    (φ q : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) (hq : ∀ i j, 0 ≤ q i j)
    (hc : SupportConnected φ q) : ∀ i, 0 < departureRate φ q i := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro i
  have hnneg : 0 ≤ departureRate φ q i := Finset.sum_nonneg (fun j _ => mul_nonneg (hφ i j) (hq i j))
  by_contra h
  have hz : departureRate φ q i=0 := le_antisymm (le_of_not_gt h) hnneg
  have hzero (j : Fin n) : φ i j*q i j=0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
      mul_nonneg (hφ i j) (hq i j))).mp hz
    exact he j (Finset.mem_univ j)
  obtain ⟨j,hji⟩ := exists_ne i
  have heq : ∀ j, Relation.ReflTransGen (fun a b => a≠b ∧ 0 < φ a b*q a b) i j → j=i := by
    intro j hp
    induction hp with
    | refl => rfl
    | @tail b c hbc hstep ih =>
      subst b
      have hh := hstep.2
      rw [hzero] at hh
      exact False.elim (lt_irrefl _ hh)
  exact hji (heq j (hc i j))

theorem stationary_product_form {n m : ℕ} [NeZero n]
    (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hc : SupportConnected φ q) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (ht : IsTraffic φ q r) (π : (Fin n → ℕ) → ℝ)
    (hπ : IsStationary n m φ (toPolicy q) π) :
    π = productForm (fun i y => r i^y) m := by
  by_cases hn : n=1
  · subst n
    have hmass : π (fun _ : Fin 1 => m)=1 := by simpa [states_one] using hπ.2.2.1
    funext x
    by_cases hx : x=(fun _ : Fin 1 => m)
    · subst x
      rw [hmass]
      simp [productForm,normConst,states_one,Fin.prod_univ_one,pow_ne_zero _ (hr 0).ne']
    · have hmem : x ∉ states 1 m := by simpa [states_one] using hx
      rw [hπ.2.1 x hmem,productForm,if_neg hmem]
  · have hn2 : 2 ≤ n := by have h := NeZero.ne n; omega
    have hmu := connected_positive_departures hn2 φ q hφ (fun i j => (hq i j).1) hc
    obtain ⟨hR,hmodel,htraffic,hconn⟩ := gordon_newell_model φ hφ q hq hmu
    exact (community_closed_product_form (departureRate φ q) (routing φ q) r hmu hR
      (hconn.mp hc) hr ((htraffic r).mp ht) m π).mp ((hmodel m π).mp hπ)

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem zero_fleet_objective {n : ℕ} (φ : Fin n → Fin n → ℝ)
    (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ) :
    obj n 0 φ I (toPolicy q) π=0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hz (i : Fin n) : x i=0 := by
    have h := Finset.single_le_sum (f:=x) (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i)
    rw [(mem_states_iff x).mp hx] at h
    omega
  simp [toPolicy,hz,rewardCurve]

theorem elevated_optimum_nonnegative {n : ℕ} (φ : Fin n → Fin n → ℝ)
    (I : Fin n → Fin n → ℝ → ℝ) (qt : Fin n → Fin n → ℝ)
    (hopt : IsRelaxOptimal φ I qt) : 0 ≤ elevObj φ I qt := by
  have hf : IsRelaxFeasible φ (fun _ _ => 0) := by
    constructor
    · intro i j; norm_num
    · intro i; simp
  have h := hopt.2 _ hf
  simpa [elevObj,rewardCurve] using h

theorem pricing_approximation {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (rewardCurve I i j))
    (qt : Fin n → Fin n → ℝ) (hopt : IsRelaxOptimal φ I qt) (hc : SupportConnected φ qt)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy qt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    (m:ℝ)/((m:ℝ)+n-1)*obj n m φ I q π ≤ obj n m φ I (toPolicy qt) πt := by
  by_cases hm0 : m=0
  · subst m
    rw [zero_fleet_objective]
    simp
  by_cases hn0 : n=0
  · subst n
    simp [obj]
  letI : NeZero n := ⟨hn0⟩
  have hm : 1 ≤ m := by omega
  let r : Fin n → ℝ := fun _ => 1
  have hr : ∀ i, 0 < r i := by intro i; norm_num [r]
  have ht : IsTraffic φ qt r := by
    intro i
    simpa [r] using hopt.1.2 i
  have hπprod := stationary_product_form φ hφ qt hopt.1.1 hc r hr ht πt hπt
  have hp : ∃ i, 0 < r i := ⟨0,hr 0⟩
  have hs : obj n m φ I (toPolicy qt) πt =
      (rmax r*G r (m-1)/G r m)*elevObj φ I qt := by
    rw [hπprod,product_objective_scale hm φ I qt r hp,
      balanced_infinite_objective φ hφ I qt hopt.1.1 hopt.1.2 hc r hr ht]
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hc0 : 0 ≤ (m:ℝ)/((m:ℝ)+n-1) := div_nonneg (by positivity) (by linarith)
  calc
    _ ≤ (m:ℝ)/((m:ℝ)+n-1)*elevObj φ I qt :=
      mul_le_mul_of_nonneg_left (relaxation_optimum_upper_bound φ hφ I hR qt hopt q π hq hπ) hc0
    _ ≤ (rmax r*G r (m-1)/G r m)*elevObj φ I qt :=
      mul_le_mul_of_nonneg_right (availability_lower_bound hm r (fun i => (hr i).le) hp)
        (elevated_optimum_nonnegative φ I qt hopt)
    _ = _ := hs.symm

end Queelius.SharedVehicle

end

section
noncomputable section
namespace Queelius.SharedVehicle
open Finset Filter QueueingFundamentals.Networks SharedVehicleApprox.Pricing
open scoped Topology

theorem positive_product_nonnegative {n m : ℕ} [NeZero n] (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℕ) :
    0 ≤ productForm (fun i y => r i^y) m x := by
  unfold productForm
  split_ifs
  · exact div_nonneg (Finset.prod_nonneg (fun i _ => (pow_pos (hr i) _).le)) (normConst_pos r hr m).le
  · rfl

theorem product_availability_le_one {n m : ℕ} [NeZero n] (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin n) :
    availability m (productForm (fun j y => r j^y) m) i ≤ 1 := by
  unfold availability tailMarginal
  calc
    _ ≤ ∑ x ∈ states n m, productForm (fun j y => r j^y) m x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => positive_product_nonnegative r hr x)
    _ = 1 := pf_sum r hr m

theorem normalization_ratio_le_one {n m : ℕ} [NeZero n] (hm : 1 ≤ m)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) : rmax r*G r (m-1)/G r m ≤ 1 := by
  rw [← product_max_availability hm r (fun i => (hr i).le)]
  exact Finset.sup'_le _ _ (fun i _ => product_availability_le_one r hr i)

theorem normalization_ratio_tendsto {n : ℕ} [NeZero n] (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Tendsto (fun m : ℕ => rmax r*G r (m-1)/G r m) atTop (𝓝 1) := by
  have hl : Tendsto (fun m : ℕ => (m:ℝ)/((m:ℝ)+n-1)) atTop (𝓝 1) := by
    simpa only [← sub_eq_add_neg,add_sub_assoc] using tendsto_natCast_div_add_atTop ((n:ℝ)-1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact availability_lower_bound hm r (fun i => (hr i).le) ⟨0,hr 0⟩
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact normalization_ratio_le_one hm r hr

theorem product_availability_tendsto {n : ℕ} [NeZero n] (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin n) :
    Tendsto (fun m => availability m (productForm (fun j y => r j^y) m) i) atTop
      (𝓝 (availInf r i)) := by
  have h := (normalization_ratio_tendsto r hr).mul_const (r i/rmax r)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [power_availability hm]
  field_simp [(rmax_positive r ⟨0,hr 0⟩).ne']

theorem stationary_availability_tendsto {n : ℕ} [NeZero n]
    (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) (hc : SupportConnected φ q)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (ht : IsTraffic φ q r)
    (πs : ℕ → (Fin n → ℕ) → ℝ) (hπs : ∀ m, IsStationary n m φ (toPolicy q) (πs m))
    (i : Fin n) : Tendsto (fun m => availability m (πs m) i) atTop (𝓝 (availInf r i)) := by
  have he (m : ℕ) : πs m = productForm (fun j y => r j^y) m :=
    stationary_product_form φ hφ q hq hc r hr ht _ (hπs m)
  simp_rw [he]
  exact product_availability_tendsto r hr i

end Queelius.SharedVehicle

end

section
set_option maxHeartbeats 1000000
noncomputable section
namespace Queelius.SharedVehicle.Controls
open Finset QueueingFundamentals.Networks SharedVehicleApprox.Pricing

theorem two_states_two : states 2 2 = {![2,0],![1,1],![0,2]} := by decide
theorem two_states_three : states 2 3 = {![3,0],![2,1],![1,2],![0,3]} := by decide

theorem removal_weights_figure :
    removalWeight 3 ![2,1] ![1,1]=2/3 ∧ removalWeight 3 ![2,1] ![2,0]=1/3 ∧
      removalWeight 3 ![3,0] ![0,2]=0 := by
  norm_num [removalWeight,Fin.sum_univ_two,funext_iff,Fin.forall_fin_two,Pi.single_apply,Matrix.vecHead,Matrix.vecTail]

theorem layer_totals_control :
    (∑ y ∈ states 2 2, removalWeight 3 ![2,1] y)=1 ∧
      (∑ x ∈ states 2 3, removalWeight 3 x ![1,1])=4/3 := by
  constructor
  · exact removalWeight_row (n:=2) (m:=3) (by norm_num) ![2,1] (by decide)
  · have h := removalWeight_column (n:=2) (m:=3) (by norm_num) ![1,1] (by decide)
    norm_num at h ⊢
    exact h

theorem balanced_bound_sharp :
    rmax (fun _ : Fin 2 => (1:ℝ)) * G (fun _ : Fin 2 => (1:ℝ)) 2 /
      G (fun _ : Fin 2 => (1:ℝ)) 3 = 3/4 := by
  norm_num [rmax,G,normConst,two_states_two,two_states_three]

theorem zero_coordinate_strict_bound :
    rmax (![1,0] : Fin 2 → ℝ) * G (![1,0] : Fin 2 → ℝ) 2 /
      G (![1,0] : Fin 2 → ℝ) 3 = 1 ∧ (3/4:ℝ)<1 := by
  have hm : rmax (![1,0] : Fin 2 → ℝ)=1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      fin_cases i <;> norm_num
    · exact Finset.le_sup' (![1,0] : Fin 2 → ℝ) (Finset.mem_univ (0 : Fin 2))
  rw [hm]
  norm_num [G,normConst,two_states_two,two_states_three,Fin.prod_univ_two]

theorem one_station_zero_rate_stationary (m : ℕ) :
    IsStationary 1 m (fun _ _ => 0) (toPolicy (fun _ _ => 0))
      (fun x => if x=(fun _ : Fin 1 => m) then 1 else 0) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x; dsimp; split_ifs <;> norm_num
  · intro x hx
    simp only [states_one,Finset.mem_singleton] at hx
    simp [hx]
  · simp [states_one]
  · intro x hx
    simp [inflowTerm,toPolicy]

theorem one_station_zero_rate_product (m : ℕ) :
    (fun x => if x=(fun _ : Fin 1 => m) then (1:ℝ) else 0) =
      productForm (fun (_ : Fin 1) (y : ℕ) => (1:ℝ)^y) m := by
  exact stationary_product_form (fun _ _ => 0) (by intros; norm_num)
    (fun _ _ => 0) (by intros; norm_num)
    (by intro i j; have h : i=j := Subsingleton.elim _ _; subst j; exact .refl)
    (fun _ => 1) (by intros; norm_num) (by intro i; simp)
    _ (one_station_zero_rate_stationary m)

end Queelius.SharedVehicle.Controls

end


theorem solution : (
  ∀ {n m : Nat} [inst : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) n],
    @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
      ∀ (r : Fin n → Real),
        (∀ (j : Fin n),
            @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (r j)) →
          (@Exists (Fin n) fun (j : Fin n) =>
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (r j)) →
            And
              (@Eq Real
                (@Finset.sup' Real (Fin n) Real.instSemilatticeSup (@Finset.univ (Fin n) (Fin.fintype n))
                  (@Finset.univ_nonempty (Fin n) (Fin.fintype n)
                    (@instNonemptyOfInhabited (Fin n) (@Fin.instInhabited n inst)))
                  fun (i : Fin n) =>
                  @SharedVehicleApprox.Pricing.availability n m
                    (@QueueingFundamentals.Networks.productForm n
                      (fun (j : Fin n) (y : Nat) =>
                        @HPow.hPow Real Nat Real
                          (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (r j) y)
                      m)
                    i)
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@SharedVehicleApprox.Pricing.rmax n inst r)
                    (@SharedVehicleApprox.Pricing.G n r
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@SharedVehicleApprox.Pricing.G n r m)))
              (@LE.le Real Real.instLE
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@Nat.cast Real Real.instNatCast m)
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@Nat.cast Real Real.instNatCast m)
                      (@Nat.cast Real Real.instNatCast n))
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@SharedVehicleApprox.Pricing.rmax n inst r)
                    (@SharedVehicleApprox.Pricing.G n r
                      (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@SharedVehicleApprox.Pricing.G n r m)))
) := @Queelius.SharedVehicle.product_max_availability_bound
