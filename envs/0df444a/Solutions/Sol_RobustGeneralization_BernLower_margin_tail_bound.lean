-- Prove2me | solution 1 for RobustGeneralization.BernLower.margin_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T08:04:41.882987+00:00
-- url     : https://prove2.me/submissions/2b5c8b6f-38a8-432b-9d27-7ba12a62ad2a

import Init
import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower.Tail
open Finset

theorem symmetric_half {Ω : Type*} [Fintype Ω]
    (q : Ω → ℝ) (hq : ∀ x, 0 ≤ q x) (hs : ∑ x, q x = 1)
    (flip : Ω ≃ Ω) (hqf : ∀ x, q (flip x) = q x)
    (noise : Ω → ℝ) (hn : ∀ x, noise (flip x) = -noise x) :
    1/2 ≤ ∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0) := by
  classical
  have heq : (∑ x, q x * (if 0 ≤ noise x then (1:ℝ) else 0)) =
      ∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0) := by
    calc
      _ = ∑ x, q (flip x) * (if 0 ≤ noise (flip x) then (1:ℝ) else 0) :=
        (Equiv.sum_comp flip _).symm
      _ = _ := by simp only [hqf,hn,neg_nonneg]
  have hbound : 1 ≤ (∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0)) +
      ∑ x, q x * (if 0 ≤ noise x then (1:ℝ) else 0) := by
    rw [← sum_add_distrib]
    calc
      1 = ∑ x, q x := hs.symm
      _ ≤ _ := by
        apply sum_le_sum
        intro x _
        by_cases h : noise x ≤ 0
        · simp only [if_pos h,mul_one]
          exact le_add_of_nonneg_right (mul_nonneg (hq x) (by split_ifs <;> norm_num))
        · have h' : 0 ≤ noise x := le_of_lt (lt_of_not_ge h)
          simp [h,h']
  linarith

theorem weighted_markov {Ω : Type*} [Fintype Ω]
    (p V : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (hV : ∀ x, 0 ≤ V x) (T γ : ℝ) (hT : 0 < T)
    (hmean : (∑ x, p x * V x) ≤ γ*T) :
    1-γ ≤ ∑ x, p x * (if V x ≤ T then (1:ℝ) else 0) := by
  classical
  have hpoint (x : Ω) : T*(p x*(1-(if V x ≤ T then (1:ℝ) else 0))) ≤ p x*V x := by
    by_cases h : V x ≤ T
    · simpa [h] using mul_nonneg (hp x) (hV x)
    · simp only [if_neg h,sub_zero,mul_one]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hp x)]
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset Ω)) => hpoint x)
  have heq : (∑ x, T*(p x*(1-(if V x ≤ T then (1:ℝ) else 0)))) =
      T*(1-∑ x, p x*(if V x ≤ T then (1:ℝ) else 0)) := by
    simp only [mul_sub,mul_one,sum_sub_distrib,← mul_sum,hs]
  rw [heq] at hsum
  nlinarith

theorem mixture_tail {Α Ω : Type*} [Fintype Α] [Fintype Ω]
    (p : Α → ℝ) (q : Ω → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (flip : Ω ≃ Ω) (hqf : ∀ x, q (flip x) = q x)
    (shift bound : Α → ℝ) (noise : Α → Ω → ℝ)
    (hbound : ∀ a, shift a ≤ bound a) (hnonneg : ∀ a, 0 ≤ bound a)
    (hn : ∀ a x, noise a (flip x) = -noise a x)
    (T γ : ℝ) (hT : 0 < T) (hmean : (∑ a, p a*bound a) ≤ γ*T) :
    (1-γ)/2 ≤ ∑ a, p a * ∑ x, q x *
      (if shift a + noise a x ≤ T then (1:ℝ) else 0) := by
  classical
  have hmark := weighted_markov p bound hp hp1 hnonneg T γ hT hmean
  have hinner (a : Α) : (1/2:ℝ)*(if bound a ≤ T then (1:ℝ) else 0) ≤
      ∑ x, q x*(if shift a+noise a x ≤ T then (1:ℝ) else 0) := by
    by_cases ha : bound a ≤ T
    · simp only [if_pos ha,mul_one]
      apply le_trans (symmetric_half q hq hq1 flip hqf (noise a) (hn a))
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hq x)
      by_cases hx : noise a x ≤ 0
      · have hx' : shift a+noise a x ≤ T := by linarith [hbound a]
        simp [hx,hx']
      · simp only [if_neg hx]
        split_ifs <;> norm_num
    · simp only [if_neg ha,mul_zero]
      exact sum_nonneg (fun x _ => mul_nonneg (hq x) (by split_ifs <;> norm_num))
  have hsum := sum_le_sum (fun a (_ : a ∈ (univ : Finset Α)) =>
    mul_le_mul_of_nonneg_left (hinner a) (hp a))
  have heq : (∑ a, p a*((1/2:ℝ)*(if bound a ≤ T then (1:ℝ) else 0))) =
      (1/2:ℝ)*∑ a, p a*(if bound a ≤ T then (1:ℝ) else 0) := by
    rw [mul_sum]; apply sum_congr rfl; intros; ring
  rw [heq] at hsum
  linarith

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset

def bitFlip {ι : Type*} : (ι → Bool) ≃ (ι → Bool) where
  toFun s i := !(s i)
  invFun s i := !(s i)
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

noncomputable def coin (r : ℝ) (b : Bool) : ℝ := if b then r else 1-r
noncomputable def mass {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, coin (r i) (s i)

@[simp] theorem coin_sum (r : ℝ) : (∑ b : Bool, coin r b) = 1 := by
  simp [coin]

theorem mass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (s : ι → Bool) : 0 ≤ mass r s := by
  apply prod_nonneg
  intro i _
  unfold coin
  split_ifs <;> linarith [(hr i).1,(hr i).2]

@[simp] theorem mass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) :
    (∑ s, mass r s) = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp [coin]

@[simp] theorem coin_half (b : Bool) : coin (1/2) b = (1/2:ℝ) := by
  cases b <;> norm_num [coin]

@[simp] theorem lab_not (b : Bool) : lab (!b) = -lab b := by
  cases b <;> norm_num [lab]

theorem product_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool → ℝ) (i : ι) (g : Bool → ℝ) :
    (∑ θ : ι → Bool, (∏ j, f j (θ j)) * g (θ i)) =
      (∑ b : Bool, f i b * g b) * ∏ j ∈ univ.erase i, ∑ b : Bool, f j b := by
  classical
  calc
    _ = ∑ θ : ι → Bool, ∏ j, f j (θ j) * (if j = i then g (θ j) else 1) := by
      apply sum_congr rfl
      intro θ _
      rw [prod_mul_distrib]
      simp
    _ = ∏ j, ∑ b : Bool, f j b * (if j = i then g b else 1) :=
      (Fintype.prod_sum (fun (j : ι) (b : Bool) => f j b * (if j = i then g b else 1))).symm
    _ = _ := by
      rw [← mul_prod_erase univ (fun j => ∑ b : Bool, f j b * (if j = i then g b else 1)) (mem_univ i)]
      simp only [ite_true]
      congr 1
      apply prod_congr rfl
      intro j hj
      simp [(mem_erase.mp hj).1]

theorem activation_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (r u : ι → ℝ) :
    (∑ a, mass r a * ∑ i, u i * (if a i then (1:ℝ) else 0)) = ∑ i, u i*r i := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  change (∑ a : ι → Bool, (∏ j, coin (r j) (a j)) * (u i * (if a i then (1:ℝ) else 0))) = _
  rw [product_coordinate (fun j b => coin (r j) b) i (fun b => u i*(if b then (1:ℝ) else 0))]
  simp [coin]
  ring

theorem product_kernel {ι Α Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Α] [Fintype Ω]
    (p : ι → Α → ℝ) (q : ι → Α → Ω → ℝ) (F : (ι → Ω) → ℝ) :
    (∑ a : ι → Α, (∏ i, p i (a i)) * ∑ x : ι → Ω, (∏ i, q i (a i) (x i))*F x) =
      ∑ x : ι → Ω, (∏ i, ∑ a : Α, p i a*q i a (x i))*F x := by
  classical
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [← mul_assoc]
  rw [← sum_mul]
  simp_rw [← prod_mul_distrib]
  congr 1
  exact (Fintype.prod_sum (fun i a => p i a*q i a (x i))).symm

theorem product_project {Ω Δ ι : Type*} [Fintype Ω] [Fintype Δ] [DecidableEq Δ]
    [Fintype ι] [DecidableEq ι] (w : ι → Ω → ℝ) (π : ι → Ω → Δ) (F : (ι → Δ) → ℝ) :
    (∑ S : ι → Ω, (∏ k, w k (S k)) * F (fun k => π k (S k))) =
      ∑ T : ι → Δ, (∏ k, ∑ x : Ω, if π k x = T k then w k x else 0) * F T := by
  classical
  have hi (S : ι → Ω) (T : ι → Δ) :
      (∏ k, if π k (S k) = T k then w k (S k) else 0) =
        if (fun k => π k (S k)) = T then ∏ k, w k (S k) else 0 := by
    by_cases h : (fun k => π k (S k)) = T
    · subst T; simp
    · rw [if_neg h]
      obtain ⟨k,hk⟩ : ∃ k, π k (S k) ≠ T k := by
        by_contra hn
        exact h (funext (fun k => by by_contra hk; exact hn ⟨k,hk⟩))
      exact prod_eq_zero (mem_univ k) (if_neg hk)
  symm
  calc
    _ = ∑ T : ι → Δ, ∑ S : ι → Ω,
        (∏ k, if π k (S k) = T k then w k (S k) else 0) * F T := by
      apply sum_congr rfl
      intro T _
      rw [Fintype.prod_sum, sum_mul]
    _ = ∑ S : ι → Ω, ∑ T : ι → Δ,
        (∏ k, if π k (S k) = T k then w k (S k) else 0) * F T := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro S _
      simp only [hi, ite_mul, zero_mul]
      simp

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem mixed_law {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) (t : ι → Bool)
    (F : (ι → Bool) → ℝ) :
    (∑ a, mass r a * ∑ s, mass (fun _ : ι => (1/2:ℝ)) s *
      F (fun i => if a i then t i else s i)) =
      ∑ z : ι → Bool, (∏ i, (1+r i*lab (t i)*lab (z i))/2)*F z := by
  classical
  calc
    _ = ∑ a : ι → Bool, (∏ i, coin (r i) (a i)) * ∑ z : ι → Bool,
        (∏ i, ∑ s : Bool, if (if a i then t i else s) = z i then coin (1/2) s else 0)*F z := by
      apply sum_congr rfl
      intro a _
      congr 1
      exact product_project (fun _ s => coin (1/2) s) (fun i s => if a i then t i else s) F
    _ = ∑ z : ι → Bool, (∏ i, ∑ a : Bool, coin (r i) a *
        ∑ s : Bool, if (if a then t i else s) = z i then coin (1/2) s else 0)*F z :=
      product_kernel (fun i (a : Bool) => coin (r i) a)
        (fun i (a z : Bool) => ∑ s : Bool, if (if a then t i else s) = z then coin (1/2) s else 0) F
    _ = _ := by
      apply sum_congr rfl
      intro z _
      congr 1
      apply prod_congr rfl
      intro i _
      cases ht : t i <;> cases hz : z i <;> simp [coin,lab,ht,hz] <;> ring

theorem signed_product_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r w : ι → ℝ) (t : ι → Bool) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T γ : ℝ) (hT : 0 < T) (hm : (∑ i, |w i| *r i) ≤ γ*T) :
    (1-γ)/2 ≤ ∑ z : ι → Bool, (∏ i, (1+r i*lab (t i)*lab (z i))/2) *
      (if (∑ i, w i*lab (z i)) ≤ T then (1:ℝ) else 0) := by
  classical
  let shift (a : ι → Bool) : ℝ := ∑ i, w i*lab (t i)*(if a i then (1:ℝ) else 0)
  let bound (a : ι → Bool) : ℝ := ∑ i, |w i| *(if a i then (1:ℝ) else 0)
  let noise (a s : ι → Bool) : ℝ := ∑ i, w i*(if a i then 0 else lab (s i))
  have hb (a : ι → Bool) : shift a ≤ bound a := by
    apply sum_le_sum
    intro i _
    cases ha : a i <;> cases ht : t i <;> simp [ha,ht,lab]
    · exact neg_le_abs (w i)
    · exact le_abs_self (w i)
  have hn (a : ι → Bool) : 0 ≤ bound a :=
    sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num))
  have hsym (a s : ι → Bool) : noise a (bitFlip s) = -noise a s := by
    simp only [noise,← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    cases ha : a i <;> simp [ha,bitFlip,lab_not]
  have hmean : (∑ a, mass r a*bound a) ≤ γ*T := by
    change (∑ a, mass r a*∑ i, |w i| *(if a i then (1:ℝ) else 0)) ≤ _
    rw [activation_mean]
    exact hm
  have h := mixture_tail (mass r) (mass (fun _ : ι => (1/2:ℝ)))
    (mass_nonneg r hr) (mass_sum r)
    (mass_nonneg _ (by intro i; norm_num)) (mass_sum _)
    bitFlip (by intro s; simp only [mass,coin_half]) shift bound noise hb hn hsym T γ hT hmean
  have hv (a s : ι → Bool) : shift a+noise a s =
      ∑ i, w i*lab (if a i then t i else s i) := by
    dsimp only [shift,noise]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases ha : a i <;> simp [ha]
  simp_rw [hv] at h
  rw [mixed_law r t (fun z => if (∑ i, w i*lab (z i)) ≤ T then (1:ℝ) else 0)] at h
  exact h

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem prodLaw_sum (d : ℕ) (μ : Fin d → ℝ) : (∑ z, prodLaw μ z) = 1 := by
  unfold prodLaw
  rw [← Fintype.prod_sum (fun i b => (1+μ i*lab b)/2)]
  have he (i : Fin d) : (∑ b : Bool, (1+μ i*lab b)/2) = 1 := by
    simp [lab]; ring
  simp only [he,prod_const_one]

theorem signed_abs (x : ℝ) : |x| *lab (decide (0 ≤ x)) = x := by
  by_cases h : 0 ≤ x
  · simp [h,lab,abs_of_nonneg h]
  · simp [h,lab,abs_of_nonpos (le_of_lt (lt_of_not_ge h))]

theorem biased_product_tail (d : ℕ) (a γ : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (μ w : Fin d → ℝ) (hμ : ∀ i, |μ i| ≤ a) (hγ : 0 < γ) :
    (1-γ)/2 ≤ ∑ z, prodLaw μ z *
      (if (∑ i, w i*lab (z i)) ≤ (a/γ)*∑ i, |w i| then (1:ℝ) else 0) := by
  classical
  by_cases ha0 : a = 0
  · have hm0 : μ = fun _ => 0 := by
      funext i
      exact abs_eq_zero.mp (le_antisymm (by simpa [ha0] using hμ i) (abs_nonneg _))
    subst μ
    have h := symmetric_half (mass (fun _ : Fin d => (1/2:ℝ)))
      (mass_nonneg _ (by intro i; norm_num)) (mass_sum _)
      bitFlip (by intro s; simp only [mass,coin_half]) (fun z => ∑ i, w i*lab (z i))
      (by intro z; simp [bitFlip,lab_not,mul_neg,← sum_neg_distrib])
    have hp (z : Fin d → Bool) : prodLaw (fun _ => (0:ℝ)) z =
        mass (fun _ : Fin d => (1/2:ℝ)) z := by simp only [prodLaw,mass,zero_mul,add_zero,coin_half]
    simp only [ha0,zero_div,zero_mul,hp]
    linarith
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hW : 0 ≤ ∑ i, |w i| := sum_nonneg (fun i _ => abs_nonneg _)
  by_cases hW0 : (∑ i, |w i|) = 0
  · have hw0 (i : Fin d) : w i = 0 := by
      apply abs_eq_zero.mp
      exact (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (univ : Finset (Fin d))) => abs_nonneg (w j))).mp hW0 i (mem_univ i)
    simp only [hw0,zero_mul,sum_const_zero,abs_zero,mul_zero,le_refl,ite_true,mul_one]
    rw [prodLaw_sum]
    linarith
  have hW' : 0 < ∑ i, |w i| := lt_of_le_of_ne hW (Ne.symm hW0)
  have hT : 0 < (a/γ)*(∑ i, |w i|) := mul_pos (div_pos ha' hγ) hW'
  have hm : (∑ i, |w i| * |μ i|) ≤ γ*((a/γ)*∑ i, |w i|) := by
    calc
      _ ≤ ∑ i, |w i| *a := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hμ i) (abs_nonneg _))
      _ = a*∑ i, |w i| := by rw [← sum_mul]; ring
      _ = _ := by field_simp <;> ring
  have h := signed_product_tail (fun i => |μ i|) w (fun i => decide (0 ≤ μ i))
    (fun i => ⟨abs_nonneg _,(hμ i).trans ha1⟩) ((a/γ)*∑ i, |w i|) γ hT hm
  simpa only [signed_abs,prodLaw] using h

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem label_product_law (d : ℕ) (τ : ℝ) (m : Fin d → ℝ) (y : Bool)
    (F : (Fin d → Bool) → ℝ) :
    (∑ θ, prodLaw m θ * ∑ s : Fin d → Bool,
      (∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) *
        F (fun i => y == s i)) =
    ∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
  classical
  calc
    _ = ∑ θ : Fin d → Bool, (∏ i, (1+m i*lab (θ i))/2) *
        ∑ z : Fin d → Bool, (∏ i, ∑ s : Bool,
          if (y == s) = z i then
            (if s = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) else 0)*F z := by
      apply sum_congr rfl
      intro θ _
      congr 1
      exact product_project
        (fun i s => if s = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)
        (fun _ s => y == s) F
    _ = ∑ z : Fin d → Bool, (∏ i, ∑ θ : Bool, (1+m i*lab θ)/2 *
        ∑ s : Bool, if (y == s) = z i then
          (if s = (y == θ) then (1/2:ℝ)+τ else 1/2-τ) else 0)*F z :=
      product_kernel (fun i (θ : Bool) => (1+m i*lab θ)/2)
        (fun _ (θ z : Bool) => ∑ s : Bool, if (y == s) = z then
          (if s = (y == θ) then (1/2:ℝ)+τ else 1/2-τ) else 0) F
    _ = _ := by
      apply sum_congr rfl
      intro z _
      congr 1
      apply prod_congr rfl
      intro i _
      cases y <;> cases hz : z i <;> simp [lab,hz] <;> ring

theorem margin_law (d : ℕ) (τ : ℝ) (m : Fin d → ℝ)
    (F : (Fin d → Bool) → ℝ) :
    (∑ θ, prodLaw m θ * ∑ p : (Fin d → Bool) × Bool,
      bernW θ τ p*F (fun i => p.2 == p.1 i)) =
      ∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
  classical
  have he (θ : Fin d → Bool) :
      (∑ p : (Fin d → Bool) × Bool, bernW θ τ p*F (fun i => p.2 == p.1 i)) =
      ∑ y : Bool, (1/2:ℝ)*∑ s : Fin d → Bool,
        (∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)*F (fun i => y == s i) := by
    rw [Fintype.sum_prod_type,sum_comm]
    simp only [bernW,mul_sum,mul_assoc]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  have hf (y : Bool) :
      (∑ θ : Fin d → Bool, ∑ s : Fin d → Bool, prodLaw m θ *
        ((1/2:ℝ)*((∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)*F (fun i => y == s i)))) =
      (1/2:ℝ)*∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
    rw [← label_product_law d τ m y F]
    simp only [mul_sum]
    apply sum_congr rfl
    intro θ _
    apply sum_congr rfl
    intro s _
    ring
  simp_rw [hf]
  simp

end RobustGeneralization.BernLower.Tail

open Finset RobustGeneralization.BernLower RobustGeneralization.BernLower.Tail

theorem solution (d : ℕ) (τ b γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (m : Fin d → ℝ) (hm : ∀ i, |m i| ≤ b) (w : E d) (hγ : 0 < γ) :
    (1 - γ) / 2 ≤ ∑ θ : Fin d → Bool, prodLaw m θ * ∑ p : (Fin d → Bool) × Bool,
      bernW θ τ p *
        (if lab p.2 * inner ℝ w (pm p.1) ≤ (2 * τ * b / γ) * ∑ i, |w i| then 1 else 0) := by
  classical
  have ha : 0 ≤ 2*τ*b := mul_nonneg (by positivity) hb
  have ha1 : 2*τ*b ≤ 1 := by nlinarith
  have hμ (i : Fin d) : |2*τ*m i| ≤ 2*τ*b := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*τ by positivity)]
    exact mul_le_mul_of_nonneg_left (hm i) (by positivity)
  have h := biased_product_tail d (2*τ*b) γ ha ha1 (fun i => 2*τ*m i) (fun i => w i) hμ hγ
  rw [← margin_law d τ m (fun z =>
    if (∑ i, w i*lab (z i)) ≤ (2*τ*b/γ)*∑ i, |w i| then (1:ℝ) else 0)] at h
  have hl (y s : Bool) : lab (y == s) = lab y*lab s := by
    cases y <;> cases s <;> norm_num [lab]
  have he (p : (Fin d → Bool) × Bool) : lab p.2*inner ℝ w (pm p.1) =
      ∑ i, w i*lab (p.2 == p.1 i) := by
    simp only [PiLp.inner_apply,pm,hl,mul_sum]
    apply sum_congr rfl
    intro i _
    change lab p.2*(lab (p.1 i)*w i) = _
    ring
  simpa only [he] using h
