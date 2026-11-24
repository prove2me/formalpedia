-- Prove2me | solution 1 for OddGoldbach19.medium_count_log260
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:53:02.215238+00:00
-- url     : https://prove2.me/submissions/6a8556f7-a14b-4921-a447-986e8c314407

import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Theorems.Thm_OddGoldbach19_twin_prime_constant_upper
import Theorems.Thm_OddGoldbach19_medium_count_log100
import Theorems.Thm_OddGoldbach19_finite_pair_sum8000
import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_OddGoldbach19_primeCounting_second_order_from25
import Theorems.Thm_OddGoldbach19_prime_pair_count_refined_five
import Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound
import Theorems.Thm_OddGoldbach19_prime_family8000
import Theorems.Thm_OddGoldbach19_table_certificate8000
/- Finite first/second-moment assembly adapted from the already accepted
odd-Goldbach21 proof; generalized here to an arbitrary finite odd-prime shift set. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset Real
namespace Medium19
open Schnir
variable (Q : Finset ℕ) (M : ℕ)
variable (hQprop : ∀ p∈Q, p.Prime ∧ p≠2 ∧ p≤M)
/-- odd primes `≤ t`. -/
def oddP (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddP_card (M : ℕ) (hM : 2 ≤ M) : (oddP M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : oddP M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [oddP, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- `[s = a + q]` with `q` an odd prime. -/
noncomputable def ind (a s : ℕ) : ℕ := if a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2 then 1 else 0

/-- number of `a ∈ Q` with `s - a` an odd prime. -/
noncomputable def Rr (s : ℕ) : ℕ := #{a ∈ Q | a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2}

theorem Rr_eq (s : ℕ) : Rr Q s = ∑ a ∈ Q, ind a s := by
  rw [Rr, card_filter]; rfl

theorem ind_sq (a s : ℕ) : ind a s * ind a s = ind a s := by
  unfold ind; split_ifs <;> simp

theorem ind_mul (a b s : ℕ) : ind a s * ind b s =
    if (a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2) ∧ (b ≤ s ∧ (s - b).Prime ∧ s - b ≠ 2) then 1 else 0 := by
  unfold ind; rw [ite_zero_mul_ite_zero, one_mul]

/-- prime pairs `m, m + d` with `m + d ≤ x` (the count in Siebert's bound). -/
noncomputable def PPs (d x : ℕ) : ℕ := #{m ∈ range (x + 1) | m.Prime ∧ (m + d).Prime ∧ m + d ≤ x}

include hQprop in
/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - M`. -/
theorem sumR_lower (n : ℕ) (hn : M + 2 ≤ n) :
    Q.card * (oddP (n - M)).card ≤ ∑ s ∈ range (n + 1), Rr Q s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Q, (oddP (n - M)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, haM⟩ := hQprop a ha
    unfold ind
    rw [← card_filter]
    apply card_le_card_of_injOn (fun q => q + a)
    · intro q hq
      simp only [oddP, coe_filter, mem_range, Set.mem_ofPred_eq] at hq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, hq.2.1, hq.2.2⟩
    · intro q _ q' _ h
      simp only at h
      omega
  calc Q.card * (oddP (n - M)).card = ∑ _a ∈ Q, (oddP (n - M)).card := by
        rw [sum_const, smul_eq_mul]
    _ ≤ _ := sum_le_sum h

/-- a pair `b < a` of shifts hits a prime pair `(s - a, s - b)`. -/
theorem pair_le (a b n : ℕ) (hba : b < a) :
    ∑ s ∈ range (n + 1), ind a s * ind b s ≤ PPs (a - b) n := by
  simp_rw [ind_mul]
  rw [← card_filter, PPs]
  apply card_le_card_of_injOn (fun s => s - a)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    obtain ⟨hs, ⟨has, hpa, -⟩, ⟨hbs, hpb, -⟩⟩ := hs
    refine ⟨by omega, hpa, ?_, by omega⟩
    rwa [show s - a + (a - b) = s - b by omega]
  · intro s hs t ht h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs ht
    simp only at h
    omega

/-- pointwise square expansion. -/
theorem Rr_sq (s : ℕ) : Rr Q s ^ 2 = Rr Q s +
    2 * ∑ a ∈ Q, ∑ b ∈ Q, if b < a then ind a s * ind b s else 0 := by
  have hsplit : ∀ a b : ℕ, ind a s * ind b s = (if b < a then ind a s * ind b s else 0) +
      (if a = b then ind a s else 0) + (if a < b then ind a s * ind b s else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp [ind_sq]
    · simp [h, h.ne', not_lt.2 h.le]
  have hsym : (∑ a ∈ Q, ∑ b ∈ Q, if a < b then ind a s * ind b s else 0) =
      ∑ a ∈ Q, ∑ b ∈ Q, if b < a then ind a s * ind b s else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have hdiag : (∑ a ∈ Q, ∑ b ∈ Q, if a = b then ind a s else 0) = ∑ a ∈ Q, ind a s :=
    sum_congr rfl fun a ha => by simp [ha]
  rw [Rr_eq, sq, sum_mul_sum]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b]
  simp only [sum_add_distrib]
  rw [hsym, hdiag]
  ring

/-- second moment: diagonal plus prime pairs. -/
theorem sumR2_le (n : ℕ) : ∑ s ∈ range (n + 1), Rr Q s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr Q s +
    2 * ∑ a ∈ Q, ∑ b ∈ Q, if b < a then PPs (a - b) n else 0 := by
  simp_rw [Rr_sq]
  rw [sum_add_distrib, ← mul_sum]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  split_ifs with h
  · exact pair_le a b n h
  · simp

include hQprop in
theorem r_pos_of_Rr (s : ℕ) (h : Rr Q s ≠ 0) : 0 < r s := by
  rw [Rr] at h
  obtain ⟨a, ha⟩ := card_pos.1 (Nat.pos_of_ne_zero h)
  rw [mem_filter] at ha
  obtain ⟨haQ, has, hp, h2⟩ := ha
  obtain ⟨hap, ha2, -⟩ := hQprop a haQ
  unfold r
  exact card_pos.2 ⟨a, mem_filter.2 ⟨mem_range.2 (by omega), hap, ha2, hp, h2⟩⟩

include hQprop in
/-- Cauchy–Schwarz. -/
theorem rv_cs (n : ℕ) : (∑ s ∈ range (n + 1), Rr Q s) ^ 2 ≤
    #{s ∈ range (n + 1) | 0 < r s} * ∑ s ∈ range (n + 1), Rr Q s ^ 2 := by
  set F := (range (n + 1)).filter (fun s => Rr Q s ≠ 0) with hF
  have h1 : ∑ s ∈ range (n + 1), Rr Q s = ∑ s ∈ F, Rr Q s := (sum_filter_ne_zero _).symm
  have h2 : ∑ s ∈ F, Rr Q s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr Q s ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : #F ≤ #{s ∈ range (n + 1) | 0 < r s} := by
    apply card_le_card
    intro s hs
    rw [hF, mem_filter] at hs
    exact mem_filter.2 ⟨hs.1, r_pos_of_Rr Q M hQprop s hs.2⟩
  rw [h1]
  calc (∑ s ∈ F, Rr Q s) ^ 2 ≤ #F * ∑ s ∈ F, Rr Q s ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul h3 h2


end Medium19
#print axioms Medium19.rv_cs
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Medium19
noncomputable def lowerX (K L : ℝ) : ℝ := K*(0.999998/L+0.45999/L^2)
noncomputable def ratio (L : ℝ) : ℝ := L/(0.999998*L+0.45999)
noncomputable def normalized (K T C A L : ℝ) : ℝ :=
  (L/K)*ratio L+(16*C*T/K^2)*(L/(L+A))*(ratio L)^2

lemma ratio_nonneg (L : ℝ) (hL : 0<L) : 0≤ratio L := by unfold ratio; positivity
lemma ratio_mono (L U : ℝ) (hL : 0<L) (hLU : L≤U) : ratio L≤ratio U := by
  have hU : 0<U := lt_of_lt_of_le hL hLU
  unfold ratio
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma normalized_mono (K T C A L U : ℝ) (hK : 0<K) (hT : 0≤T)
    (hC : 0≤C) (hA : 0≤A) (hL : 0<L) (hLU : L≤U) :
    normalized K T C A L≤normalized K T C A U := by
  have hU : 0<U := lt_of_lt_of_le hL hLU
  have hr := ratio_mono L U hL hLU
  have hr0 := ratio_nonneg L hL
  have hR0 := ratio_nonneg U hU
  have hfrac : L/(L+A)≤U/(U+A) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hLU)]
  unfold normalized
  apply add_le_add
  · exact mul_le_mul (div_le_div_of_nonneg_right hLU hK.le) hr hr0 (by positivity)
  · have hh := mul_le_mul hfrac (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _) (by positivity : 0≤U/(U+A))
    have hp : 0≤16*C*T/K^2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hh hp
    nlinarith

lemma normalized_identity (K T C A L : ℝ) (hK : 0<K) (hL : 0<L) (hA : 0≤A) :
    normalized K T C A L=
      (lowerX K L+16*C*T/(L*(L+A)))/(lowerX K L)^2 := by
  have hp : 0<0.999998*L+0.45999 := by positivity
  have hLA : 0<L+A := by positivity
  unfold normalized ratio lowerX
  field_simp <;> ring

theorem endpoint_criterion (K T C A L U : ℝ) (hK : 0<K) (hT : 0≤T)
    (hC : 0≤C) (hA : 0≤A) (hL : 0<L) (hLU : L≤U)
    (hend : normalized K T C A U≤17.99) :
    lowerX K L+16*C*T/(L*(L+A))≤17.99*(lowerX K L)^2 := by
  have hh := (normalized_mono K T C A L U hK hT hC hA hL hLU).trans hend
  rw [normalized_identity K T C A L hK hL hA] at hh
  have hx : 0<lowerX K L := by unfold lowerX; positivity
  exact (div_le_iff₀ (sq_pos_of_pos hx)).mp hh

lemma low_endpoint : normalized 1000 867861 1.3204 0 40≤17.99 := by
  norm_num [normalized,ratio]
lemma middle_endpoint : normalized 1000 867861 1.3204 4 100≤17.99 := by
  norm_num [normalized,ratio]
lemma high_endpoint : normalized 8000 55737000 1.3204 5.5 260≤17.99 := by
  norm_num [normalized,ratio]

theorem count_from_moments (n X Y cnt x k : ℝ) (hn : 0<n) (hx : 0<x)
    (hk : 0≤k) (hc : 0≤cnt) (hX : n*x≤X) (hY : Y≤n*k)
    (hcs : X^2≤cnt*(X+Y)) (hnum : x+k≤17.99*x^2)
    (hmono : (100/1799:ℝ)≤2*x) : n*(100/1799:ℝ)≤cnt := by
  have hXp : 0<X := lt_of_lt_of_le (mul_pos hn hx) hX
  have hnk : 0≤n*k := mul_nonneg hn.le hk
  by_contra hcon
  push Not at hcon
  have hupper : X^2<n*(100/1799:ℝ)*(X+n*k) := by
    have hh := mul_le_mul_of_nonneg_left (show X+Y≤X+n*k by linarith) hc
    have ht := mul_lt_mul_of_pos_right hcon (show 0<X+n*k by linarith)
    linarith
  have p1 : 0≤(X-n*x)*(X+n*x-n*(100/1799:ℝ)) := by
    apply mul_nonneg (by linarith)
    have hm := mul_le_mul_of_nonneg_left hmono hn.le
    linarith
  have p2 : 0≤n^2*(17.99*x^2-x-k) := mul_nonneg (sq_nonneg _) (by linarith)
  have he : X^2-n*(100/1799:ℝ)*(X+n*k)=
      (X-n*x)*(X+n*x-n*(100/1799:ℝ))+n^2*(17.99*x^2-x-k)*(100/1799:ℝ) := by ring
  linarith
end Medium19
#print axioms Medium19.endpoint_criterion
set_option autoImplicit false
open scoped BigOperators
namespace Medium19
noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p∈s.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1

theorem Kf_nonneg (s : ℕ) : 0≤Kf s := by
  unfold Kf
  apply Finset.prod_nonneg
  intro p hp
  split_ifs with h
  · have hpR : (2:ℝ)<p := by exact_mod_cast h
    apply div_nonneg <;> linarith
  · norm_num

theorem Kf_double (m : ℕ) : Kf (2*m)=Kf m := by
  by_cases hm : m=0
  · subst m
    norm_num [Kf]
  unfold Kf
  rw [←Finset.prod_filter,←Finset.prod_filter]
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp,hdiv,hzero⟩,hp2⟩
      refine ⟨⟨hp,?_,hm⟩,hp2⟩
      rcases hp.dvd_mul.mp hdiv with hh|hh
      · have hh2 : p≤2 := Nat.le_of_dvd (by norm_num) hh
        omega
      · exact hh
    · rintro ⟨⟨hp,hdiv,hzero⟩,hp2⟩
      exact ⟨⟨hp,hdiv.mul_left 2,by omega⟩,hp2⟩
  · intro p hp
    rfl
end Medium19
#print axioms Medium19.Kf_double
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Real
namespace Medium19

theorem first_moment (Q : Finset ℕ) (M n : ℕ)
    (hQprop : ∀ p∈Q, p.Prime ∧ p≠2 ∧ p≤M)
    (hM : M≤100000) (hln : 26≤log (n:ℝ)) (hlu : log (n:ℝ)≤260) :
    lowerX (Q.card:ℝ) (log (n:ℝ))*(n:ℝ) ≤
      ((∑ s∈Finset.range (n+1), Rr Q s : ℕ):ℝ) := by
  have hnpos : 0<n := by
    by_contra hh
    have hz : n=0 := by omega
    subst n
    norm_num at hln
  have hnR : (0:ℝ)<n := by exact_mod_cast hnpos
  have hN : (100000000000:ℝ)≤n := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2.7)
      (show (2.7:ℝ)≤exp 1 by linarith [exp_one_gt_d9]) 26
    have he : exp 26=exp 1^26 := by rw [←exp_nat_mul]; norm_num
    rw [←he] at hp
    have hnum : (100000000000:ℝ)≤2.7^26 := by norm_num
    have hex : exp 26≤(n:ℝ) := (le_log_iff_exp_le hnR).mp hln
    linarith
  have hMR : (M:ℝ)≤100000 := by exact_mod_cast hM
  have hM0 : (0:ℝ)≤M := Nat.cast_nonneg M
  have hMN : M≤n := by exact_mod_cast (show (M:ℝ)≤n by linarith)
  set m:=n-M with hm
  have hmR : (m:ℝ)=(n:ℝ)-(M:ℝ) := by rw [hm,Nat.cast_sub hMN]
  have hm0 : (0:ℝ)< m := by rw [hmR]; linarith
  have hm2 : 2≤ m := by exact_mod_cast (show (2:ℝ)≤ m by rw [hmR]; linarith)
  have hex25 : exp 25≤(100000000000-100000:ℝ) := by
    have hp := pow_le_pow_left₀ (exp_pos 1).le
      (show exp 1≤(2.72:ℝ) by linarith [exp_one_lt_d9]) 25
    have he : exp 25=exp 1^25 := by rw [←exp_nat_mul]; norm_num
    rw [←he] at hp
    have hh : (2.72:ℝ)^25≤100000000000-100000 := by norm_num
    linarith
  have hmlog : 25≤log (m:ℝ) := (le_log_iff_exp_le hm0).mpr (by rw [hmR]; linarith)
  have hmlog0 : 0<log (m:ℝ) := by linarith
  have hL0 : 0<log (n:ℝ) := by linarith
  have hlogs : log (m:ℝ)≤log (n:ℝ) := log_le_log hm0 (by rw [hmR]; linarith)
  have hpi := OddGoldbach19.primeCounting_second_order_from25 m hmlog
  have hp1 : (m:ℝ)/log (n:ℝ)≤(m:ℝ)/log m :=
    div_le_div_of_nonneg_left hm0.le hmlog0 hlogs
  have hp2 : 0.46*(m:ℝ)/(log (n:ℝ))^2≤0.46*(m:ℝ)/(log m)^2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hmlog0.le hlogs 2)
  have hmd : 0.999999*(n:ℝ)≤ m := by rw [hmR]; linarith
  have hgap : (1:ℝ)≤0.000001*n/log (n:ℝ) := by
    rw [le_div_iff₀ hL0]
    linarith
  have hf : 0.999998*(n:ℝ)/log (n:ℝ)+1≤(m:ℝ)/log (n:ℝ) := by
    have hh := div_le_div_of_nonneg_right hmd hL0.le
    have he : 0.999999*(n:ℝ)/log (n:ℝ)=
        0.999998*(n:ℝ)/log (n:ℝ)+0.000001*(n:ℝ)/log (n:ℝ) := by ring
    rw [he] at hh
    linarith
  have hs : 0.45999*(n:ℝ)/(log (n:ℝ))^2≤0.46*(m:ℝ)/(log (n:ℝ))^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  have hcard : ((oddP m).card:ℝ)+1=(Nat.primeCounting m:ℝ) := by
    exact_mod_cast oddP_card m hm2
  have hsmall : (0.999998/log (n:ℝ)+0.45999/(log (n:ℝ))^2)*(n:ℝ)≤((oddP m).card:ℝ) := by
    have he : (0.999998/log (n:ℝ)+0.45999/(log (n:ℝ))^2)*(n:ℝ)=
        0.999998*(n:ℝ)/log (n:ℝ)+0.45999*(n:ℝ)/(log (n:ℝ))^2 := by ring
    rw [he]
    linarith
  have hsum := sumR_lower Q M hQprop n (by exact_mod_cast (show (M:ℝ)+2≤n by linarith))
  have hsumR : (Q.card:ℝ)*((oddP m).card:ℝ)≤
      ((∑ s∈Finset.range (n+1),Rr Q s:ℕ):ℝ) := by exact_mod_cast hsum
  have hmul := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg Q.card : (0:ℝ)≤Q.card)
  unfold lowerX
  nlinarith
end Medium19
#print axioms Medium19.first_moment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Finset Real
namespace Medium19

def AdmissibleShift (n : ℕ) (A : ℝ) : Prop :=
  A=0 ∨ (A=4 ∧ 40≤log (n:ℝ)) ∨ (A=5.5 ∧ 100≤log (n:ℝ))

theorem pair_bound (n d : ℕ) (hd0 : 0<d) (hd : 2∣d)
    (hl : 26≤log (n:ℝ)) (A : ℝ) (hA : AdmissibleShift n A) :
    (PPs d n:ℝ)≤8*TaoFivePrimes.twinPrimeConstant*n/
      (log (n:ℝ)*(log (n:ℝ)+A))*Kf d := by
  have hn0 : 0<n := by
    by_contra hh
    have hz : n=0 := by omega
    subst n
    norm_num at hl
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hn5 : 5≤n := by
    by_contra hh
    have hb : (n:ℝ)≤4 := by exact_mod_cast (show n≤4 by omega)
    have hlog := log_le_sub_one_of_pos hnR
    linarith
  have he : (PPs d n:ℝ)=(∑ m∈range (n+1),
      if m.Prime ∧ (m+d).Prime ∧ m+d≤n then (1:ℝ) else 0) := by
    rw [PPs,Finset.natCast_card_filter]
  rw [he]
  rcases hA with ha|⟨ha,h40⟩|⟨ha,h100⟩
  · subst A
    have hh := TaoFivePrimes.siebert_prime_pair_bound n d (by omega) hd0 hd
    convert hh using 1 <;> (unfold Kf; ring)
  · subst A
    have hh := (OddGoldbach19.prime_pair_count_refined_five n d hn5 hd0 hd h40).1
    convert hh using 1 <;> (unfold Kf; ring)
  · subst A
    have hh := (OddGoldbach19.prime_pair_count_refined_five n d hn5 hd0 hd (by linarith)).2 h100
    convert hh using 1 <;> (unfold Kf; ring)

theorem off_diagonal (Q : Finset ℕ) (n : ℕ) (T CU A : ℝ)
    (hQ : ∀ p∈Q, p.Prime ∧ p≠2) (hT0 : 0≤T)
    (hT : (∑ a∈Q,∑ b∈Q,if b<a then Kf (a-b) else 0)≤T)
    (hCU : TaoFivePrimes.twinPrimeConstant≤CU)
    (hl : 26≤log (n:ℝ)) (hA0 : 0≤A) (hA : AdmissibleShift n A) :
    ((2*∑ a∈Q,∑ b∈Q,if b<a then PPs (a-b) n else 0:ℕ):ℝ)≤
      (n:ℝ)*(16*CU*T/(log (n:ℝ)*(log (n:ℝ)+A))) := by
  have hC0 : 0≤TaoFivePrimes.twinPrimeConstant := by
    have hh := PrimePairSieve.sieve_constants_certificate.1
    linarith
  have hCU0 : 0≤CU := hC0.trans hCU
  have hL0 : 0<log (n:ℝ) := by linarith
  let D:=log (n:ℝ)*(log (n:ℝ)+A)
  have hD0 : 0<D := by dsimp [D]; positivity
  let w:=8*TaoFivePrimes.twinPrimeConstant*n/D
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hterm : ∀ a∈Q,∀ b∈Q,((if b<a then PPs (a-b) n else 0:ℕ):ℝ)≤
      w*(if b<a then Kf (a-b) else 0) := by
    intro a ha b hb
    obtain ⟨hap,ha2⟩ := hQ a ha
    obtain ⟨hbp,hb2⟩ := hQ b hb
    split_ifs with hab
    · have hao := hap.odd_of_ne_two ha2
      have hbo := hbp.odd_of_ne_two hb2
      have hev : 2∣a-b := by
        obtain ⟨i,hi⟩ := hao
        obtain ⟨j,hj⟩ := hbo
        exact ⟨i-j,by omega⟩
      exact pair_bound n (a-b) (by omega) hev hl A hA
    · simp
  have hsum : ((∑ a∈Q,∑ b∈Q,if b<a then PPs (a-b) n else 0:ℕ):ℝ)≤w*T := by
    have hcast : ((∑ a∈Q,∑ b∈Q,if b<a then PPs (a-b) n else 0:ℕ):ℝ)=
        ∑ a∈Q,∑ b∈Q,((if b<a then PPs (a-b) n else 0:ℕ):ℝ) := by
      rw [Nat.cast_sum]
      exact sum_congr rfl (fun a ha=>Nat.cast_sum _ _)
    rw [hcast]
    calc
      _ ≤∑ a∈Q,∑ b∈Q,w*(if b<a then Kf (a-b) else 0) :=
        sum_le_sum (fun a ha=>sum_le_sum (fun b hb=>hterm a ha b hb))
      _ =w*(∑ a∈Q,∑ b∈Q,if b<a then Kf (a-b) else 0) := by
        rw [mul_sum]
        exact sum_congr rfl (fun a ha=>(mul_sum _ _ _).symm)
      _ ≤_ := mul_le_mul_of_nonneg_left hT hw0
  have hw : w≤8*CU*n/D := by
    dsimp [w]
    apply div_le_div_of_nonneg_right _ hD0.le
    have hh := mul_le_mul_of_nonneg_right hCU (show (0:ℝ)≤8*n by positivity)
    nlinarith
  have hwt := mul_le_mul_of_nonneg_right hw hT0
  have he : (n:ℝ)*(16*CU*T/D)=2*(8*CU*n/D*T) := by ring
  change _≤(n:ℝ)*(16*CU*T/D)
  rw [he]
  push_cast
  push_cast at hsum
  nlinarith
end Medium19
#print axioms Medium19.off_diagonal
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Finset Real
namespace Medium19

theorem criterion (Q : Finset ℕ) (M n : ℕ) (T CU A U : ℝ)
    (hQprop : ∀ p∈Q, p.Prime ∧ p≠2 ∧ p≤M)
    (hcard : 1000≤Q.card) (hM : M≤100000)
    (hT0 : 0≤T) (hT : (∑ a∈Q,∑ b∈Q,if b<a then Kf (a-b) else 0)≤T)
    (hCU : TaoFivePrimes.twinPrimeConstant≤CU) (hA0 : 0≤A)
    (hA : AdmissibleShift n A) (hln : 26≤log (n:ℝ)) (hlu : log (n:ℝ)≤U)
    (hU : U≤260) (hend : normalized (Q.card:ℝ) T CU A U≤17.99) :
    (n:ℝ)*(100/1799:ℝ)≤(((range (n+1)).filter (fun s=>0<Schnir.r s)).card:ℝ) := by
  have hL0 : 0<log (n:ℝ) := by linarith
  have hK1000 : (1000:ℝ)≤Q.card := by exact_mod_cast hcard
  have hK0 : (0:ℝ)<Q.card := by linarith
  have hC0 : 0≤TaoFivePrimes.twinPrimeConstant := by
    have hh := PrimePairSieve.sieve_constants_certificate.1
    linarith
  have hCU0 : 0≤CU := hC0.trans hCU
  have hn0 : 0<n := by
    by_contra hh
    have hz : n=0 := by omega
    subst n
    norm_num at hln
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  let X : ℕ:=∑ s∈range (n+1),Rr Q s
  let Y : ℕ:=2*∑ a∈Q,∑ b∈Q,if b<a then PPs (a-b) n else 0
  let cnt : ℕ:=((range (n+1)).filter (fun s=>0<Schnir.r s)).card
  have hX := first_moment Q M n hQprop hM hln (hlu.trans hU)
  change lowerX (Q.card:ℝ) (log (n:ℝ))*(n:ℝ)≤(X:ℝ) at hX
  have hY := off_diagonal Q n T CU A
    (fun p hp=>⟨(hQprop p hp).1,(hQprop p hp).2.1⟩) hT0 hT hCU hln hA0 hA
  change (Y:ℝ)≤(n:ℝ)*(16*CU*T/(log (n:ℝ)*(log (n:ℝ)+A))) at hY
  have hcsN := (rv_cs Q M hQprop n).trans
    (Nat.mul_le_mul_left _ (sumR2_le Q n))
  have hcsR : (X:ℝ)^2≤(cnt:ℝ)*((X:ℝ)+(Y:ℝ)) := by exact_mod_cast hcsN
  have hnum := endpoint_criterion (Q.card:ℝ) T CU A (log (n:ℝ)) U
    hK0 hT0 hCU0 hA0 hL0 hlu hend
  have hx : 0<lowerX (Q.card:ℝ) (log (n:ℝ)) := by unfold lowerX; positivity
  have hk : 0≤16*CU*T/(log (n:ℝ)*(log (n:ℝ)+A)) := by positivity
  have hmono : (100/1799:ℝ)≤2*lowerX (Q.card:ℝ) (log (n:ℝ)) := by
    have hf : (0.999998:ℝ)/260≤0.999998/log (n:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hL0 (hlu.trans hU)
    have hs : (0:ℝ)≤0.45999/(log (n:ℝ))^2 := by positivity
    have hh := mul_le_mul hK1000
      (show (0.999998:ℝ)/260≤0.999998/log (n:ℝ)+0.45999/(log (n:ℝ))^2 by linarith)
      (by norm_num : (0:ℝ)≤0.999998/260) hK0.le
    unfold lowerX
    nlinarith
  have hh := count_from_moments (n:ℝ) X Y cnt
    (lowerX (Q.card:ℝ) (log (n:ℝ))) (16*CU*T/(log (n:ℝ)*(log (n:ℝ)+A)))
    hnR hx hk (Nat.cast_nonneg _) (by simpa only [mul_comm] using hX) hY hcsR hnum hmono
  exact hh
end Medium19
#print axioms Medium19.criterion
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open scoped BigOperators
open Finset Real OddGoldbach19.Cert8000 Medium19
namespace Certificate8000Bridge

def Qs : Finset ℕ :=⟨(Qlist:Multiset ℕ),
  Multiset.coe_nodup.mpr OddGoldbach19.prime_family8000.2.1⟩

theorem Qs_prop (p : ℕ) (hp : p∈Qs) : p.Prime ∧ p≠2 ∧ p≤81817 := by
  have h : p∈Qlist := Multiset.mem_coe.mp (Finset.mem_def.mp hp)
  exact OddGoldbach19.prime_family8000.1 p h

theorem Qs_card : Qs.card=8000 := by
  show Multiset.card (Qlist:Multiset ℕ)=8000
  rw [Multiset.coe_card]
  exact OddGoldbach19.prime_family8000.2.2

lemma kr_cast (d : ℕ) : (KR d:ℝ)=Kf d := by
  simp only [KR,Kf,Rat.cast_prod]
  apply prod_congr rfl
  intro p hp
  split_ifs <;> push_cast <;> rfl

lemma wc_bound (d : ℕ) : Kf d≤(WC d:ℝ)/10000 := by
  have hh : 10000*KR d≤(WC d:ℚ) := by
    have hi : (⌈10000*KR d⌉:ℤ)≤(WC d:ℤ) := by unfold WC;omega
    exact (Int.le_ceil _).trans (by exact_mod_cast hi)
  have hr : (10000:ℝ)*(KR d:ℝ)≤(WC d:ℝ) := by exact_mod_cast hh
  rw [kr_cast] at hr
  linarith

lemma wp_bound (d : ℕ) (hd : d<40909) : Kf d≤(WP d:ℝ)/10000 := by
  have hh : (WC d:ℝ)≤WP d := by exact_mod_cast OddGoldbach19.table_certificate8000 d hd
  linarith [wc_bound d]

theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ→M) :
    ∑ a∈Qs,f a=(Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist:Multiset ℕ))=_
  rw [Multiset.map_coe,Multiset.sum_coe]

theorem certificate_from_sum
    (hpair : (Qlist.map fun a=>(Qlist.map fun b=>if b<a then WP ((a-b)/2) else 0).sum).sum≤557349373474) :
    ∃ Q : Finset ℕ, Q.card=8000 ∧
      (∀ p∈Q,p.Prime ∧ p≠2 ∧ p≤81817) ∧
      (∑ a∈Q,∑ b∈Q,if b<a then Kf (a-b) else 0)≤(55737000:ℝ) := by
  refine ⟨Qs,Qs_card,Qs_prop,?_⟩
  have hterm : ∀ a∈Qs,∀ b∈Qs,(if b<a then Kf (a-b) else 0)≤
      ((if b<a then WP ((a-b)/2) else 0:ℕ):ℝ)/10000 := by
    intro a ha b hb
    have hap := Qs_prop a ha
    have hbp := Qs_prop b hb
    split_ifs with hab
    · have hao : a%2=1 := Nat.odd_iff.mp (hap.1.odd_of_ne_two hap.2.1)
      have hbo : b%2=1 := Nat.odd_iff.mp (hbp.1.odd_of_ne_two hbp.2.1)
      have hd : a-b=2*((a-b)/2) := by omega
      have he : Kf (a-b)=Kf ((a-b)/2) :=
        (congrArg Kf hd).trans (Kf_double ((a-b)/2))
      rw [he]
      exact wp_bound _ (by omega)
    · simp
  have hnat : (∑ a∈Qs,∑ b∈Qs,if b<a then WP ((a-b)/2) else 0:ℕ)≤557349373474 := by
    rw [sum_Qs]
    simp_rw [sum_Qs]
    exact hpair
  have hHle : ((∑ a∈Qs,∑ b∈Qs,if b<a then WP ((a-b)/2) else 0:ℕ):ℝ)≤557349373474 := by
    exact_mod_cast hnat
  have hc : ((∑ a∈Qs,∑ b∈Qs,if b<a then WP ((a-b)/2) else 0:ℕ):ℝ)=
      ∑ a∈Qs,∑ b∈Qs,((if b<a then WP ((a-b)/2) else 0:ℕ):ℝ) := by
    rw [Nat.cast_sum]
    exact sum_congr rfl fun a _=>Nat.cast_sum _ _
  have hsum := sum_le_sum (s:=Qs) (fun a ha=>sum_le_sum (s:=Qs) (fun b hb=>hterm a ha b hb))
  simp_rw [←sum_div] at hsum
  rw [←hc] at hsum
  linarith
end Certificate8000Bridge
#print axioms Certificate8000Bridge.certificate_from_sum
open Medium19 Finset Real
namespace OddGoldbach19
theorem high_count_from_certificate
    (hcert : ∃ Q : Finset ℕ, Q.card=8000 ∧
      (∀ p∈Q,p.Prime ∧ p≠2 ∧ p≤81817) ∧
      (∑ a∈Q,∑ b∈Q,if b<a then Kf (a-b) else 0)≤(55737000:ℝ))
    (n : ℕ) (hln : 100≤log (n:ℝ)) (hlu : log (n:ℝ)≤260) :
    (n:ℝ)*(100/1799:ℝ)≤(((range (n+1)).filter (fun s=>0<Schnir.r s)).card:ℝ) := by
  obtain ⟨Q,hcard,hQprop,hT⟩ := hcert
  apply criterion Q 81817 n 55737000 1.3204 5.5 260 hQprop (by omega) (by norm_num)
    (by norm_num) hT twin_prime_constant_upper (by norm_num)
    (Or.inr (Or.inr ⟨rfl,hln⟩)) (by linarith) hlu (by norm_num)
  rw [hcard]
  exact high_endpoint


end OddGoldbach19

set_option autoImplicit false
open Finset Real
theorem solution (n : ℕ)
    (hlo : 26≤log (n:ℝ)) (hhi : log (n:ℝ)≤260) :
    (n:ℝ)*(100/1799:ℝ)≤(((range (n+1)).filter (fun s=>0<Schnir.r s)).card:ℝ) := by
  by_cases h100 : log (n:ℝ)≤100
  · exact OddGoldbach19.medium_count_log100 n hlo h100
  · exact OddGoldbach19.high_count_from_certificate
      (Certificate8000Bridge.certificate_from_sum OddGoldbach19.finite_pair_sum8000)
      n (by linarith) hhi
#print axioms solution
