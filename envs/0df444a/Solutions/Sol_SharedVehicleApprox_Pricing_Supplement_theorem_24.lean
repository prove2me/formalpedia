-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_24
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:30.0768+00:00
-- url     : https://prove2.me/submissions/d2cf70c0-7118-4493-8fa4-6e1fe24d010d

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_MultiObjective

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 24, p. 29 (corrected: the support graph of `q̃` is strongly connected, unless
`q̃ = 0`): with `γ = m/(m+n−1)`, the output `q̃` of Algorithm 5 satisfies `Φ_m(q̃) ≥ γ Opt_m`, where
`Opt_m` is over state-dependent policies with `Ψ_m ≥ c`, and `Ψ_m(q̃) ≥ γ c`. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (IΦ IΨ : Fin n → Fin n → ℝ → ℝ)
    (hΦ : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve IΦ i j))
    (hΨ : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve IΨ i j))
    (c : ℝ) (hc : 0 ≤ c)
    (qt : Fin n → Fin n → ℝ) (hopt : IsAlg5Optimal φ IΦ IΨ c qt)
    (hconn : SupportConnected φ qt ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy qt) πt) :
    (∀ (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ),
      IsPolicy n m q → IsStationary n m φ q π → c ≤ obj n m φ IΨ q π →
        (m : ℝ) / ((m : ℝ) + n - 1) * obj n m φ IΦ q π ≤ obj n m φ IΦ (toPolicy qt) πt) ∧
      (m : ℝ) / ((m : ℝ) + n - 1) * c ≤ obj n m φ IΨ (toPolicy qt) πt := by
        classical
        have hmem : ∀ {N : ℕ} (x : Fin n → ℕ), x ∈ states n N ↔ ∑ k, x k = N := by
          intro N x
          simp only [states, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨fun i => ?_, h⟩
            have := Finset.single_le_sum (f := x) (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
        have hmove : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j →
            moveState x i j + Pi.single j 1 = x + Pi.single i 1 := by
          intro x i j hij hj
          funext k
          simp only [moveState, Pi.add_apply, Pi.single_apply, Function.update_apply]
          by_cases hki : k = i
          · subst hki; simp [hij]
          · by_cases hkj : k = j
            · subst hkj; simp [hki]; omega
            · simp [hki, hkj]
        have hsum_move : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j →
            ∑ k, moveState x i j k = ∑ k, x k := by
          intro x i j hij hj
          have h := congrArg (fun f : Fin n → ℕ => ∑ k, f k) (hmove x i j hij hj)
          simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
            if_true] at h
          omega
        have hmove_i : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → moveState x i j i = x i + 1 := by
          intro x i j hij; simp [moveState]
        have hmove_inv : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j →
            moveState (moveState x i j) j i = x := by
          intro x i j hij hj; funext k
          simp only [moveState, Function.update_apply]
          by_cases hki : k = i
          · subst hki; simp [hij]
          · by_cases hkj : k = j
            · subst hkj; simp [hki]; omega
            · simp [hki, hkj]
        have hbij : ∀ (N : ℕ) (i j : Fin n), i ≠ j → ∀ g : (Fin n → ℕ) → (Fin n → ℕ) → ℝ,
            ∑ x ∈ (states n N).filter (fun x => 1 ≤ x j), g x (moveState x i j) =
            ∑ y ∈ (states n N).filter (fun y => 1 ≤ y i), g (moveState y j i) y := by
          intro N i j hij g
          apply Finset.sum_nbij' (fun x => moveState x i j) (fun y => moveState y j i)
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter, hmem] at hx ⊢
            exact ⟨by rw [hsum_move x i j hij hx.2]; exact hx.1, by rw [hmove_i x i j hij]; omega⟩
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_filter, hmem] at hy ⊢
            exact ⟨by rw [hsum_move y j i (Ne.symm hij) hy.2]; exact hy.1,
              by rw [hmove_i y j i (Ne.symm hij)]; omega⟩
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx
            exact hmove_inv x i j hij hx.2
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_filter] at hy
            exact hmove_inv y j i (Ne.symm hij) hy.2
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx
            rw [hmove_inv x i j hij hx.2]
        have hflow : ∀ (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ),
            IsPolicy n m q → IsStationary n m φ q π → ∀ k,
            ∑ i, φ i k * (∑ x ∈ states n m, π x * q x i k) =
              ∑ j, φ k j * (∑ x ∈ states n m, π x * q x k j) := by
          intro q π hq hπ k
          obtain ⟨_, _, _, hbal⟩ := hπ
          let F : (Fin n → ℕ) → ℝ := fun x => (x k : ℝ)
          have key : ∀ i j, ∑ x ∈ states n m, F x * inflowTerm φ q π x i j =
              ∑ y ∈ states n m, (F y + (if k = j then 1 else 0) - (if k = i then 1 else 0)) *
                (π y * φ i j * q y i j) := by
            intro i j
            by_cases hij : i = j
            · subst hij
              simp only [inflowTerm, if_true]
              apply Finset.sum_congr rfl; intro x _; ring
            · have e1 : ∑ x ∈ states n m, F x * inflowTerm φ q π x i j =
                  ∑ x ∈ (states n m).filter (fun x => 1 ≤ x j),
                    F x * (π (moveState x i j) * φ i j * q (moveState x i j) i j) := by
                rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _
                simp only [inflowTerm, hij, if_false]; split_ifs <;> simp
              rw [e1, hbij m i j hij (fun x y => F x * (π y * φ i j * q y i j))]
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl; intro y hy
              by_cases h1 : 1 ≤ y i
              · rw [if_pos h1]
                congr 1
                simp only [F, moveState, Function.update_apply]
                by_cases hkj : k = j
                · subst hkj; simp [Ne.symm hij]
                · by_cases hki : k = i
                  · subst hki; simp [hkj]; rw [Nat.cast_sub h1]; ring
                  · simp [hki, hkj]
              · rw [if_neg h1]
                have : y i = 0 := by omega
                rw [(hq y hy i j).2.2 this]; ring
          have total : ∑ x ∈ states n m, F x * (π x * ∑ i, ∑ j, φ i j * q x i j) =
              ∑ x ∈ states n m, F x * ∑ i, ∑ j, inflowTerm φ q π x i j :=
            Finset.sum_congr rfl (fun x hx => by rw [hbal x hx])
          have rhs : ∑ x ∈ states n m, F x * ∑ i, ∑ j, inflowTerm φ q π x i j =
              ∑ i, ∑ j, ∑ y ∈ states n m, (F y + (if k = j then 1 else 0) - (if k = i then 1 else 0)) *
                (π y * φ i j * q y i j) := by
            calc ∑ x ∈ states n m, F x * ∑ i, ∑ j, inflowTerm φ q π x i j
                = ∑ x ∈ states n m, ∑ i, ∑ j, F x * inflowTerm φ q π x i j := by
                  simp_rw [Finset.mul_sum]
              _ = ∑ i, ∑ x ∈ states n m, ∑ j, F x * inflowTerm φ q π x i j := Finset.sum_comm
              _ = ∑ i, ∑ j, ∑ x ∈ states n m, F x * inflowTerm φ q π x i j := by
                  apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
              _ = _ := by
                  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
                  exact key i j
          have lhs : ∑ x ∈ states n m, F x * (π x * ∑ i, ∑ j, φ i j * q x i j) =
              ∑ i, ∑ j, ∑ y ∈ states n m, F y * (π y * φ i j * q y i j) := by
            calc ∑ x ∈ states n m, F x * (π x * ∑ i, ∑ j, φ i j * q x i j)
                = ∑ x ∈ states n m, ∑ i, ∑ j, F x * (π x * φ i j * q x i j) := by
                  apply Finset.sum_congr rfl; intro x _
                  simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
                  apply Finset.sum_congr rfl; intro j _; ring
              _ = ∑ i, ∑ x ∈ states n m, ∑ j, F x * (π x * φ i j * q x i j) := Finset.sum_comm
              _ = _ := by
                  apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
          let X : Fin n → Fin n → ℝ := fun i j => ∑ y ∈ states n m, π y * φ i j * q y i j
          have split : ∑ i, ∑ j, ∑ y ∈ states n m,
              (F y + (if k = j then 1 else 0) - (if k = i then 1 else 0)) * (π y * φ i j * q y i j) =
              ∑ i, ∑ j, ∑ y ∈ states n m, F y * (π y * φ i j * q y i j) +
                (∑ i, ∑ j, (if k = j then 1 else 0) * X i j - ∑ i, ∑ j, (if k = i then 1 else 0) * X i j) := by
            simp only [X, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring
          have e2 : ∑ i, ∑ j, (if k = j then (1:ℝ) else 0) * X i j = ∑ i, X i k := by
            apply Finset.sum_congr rfl; intro i _
            simp [Finset.sum_ite_eq]
          have e3 : ∑ i, ∑ j, (if k = i then (1:ℝ) else 0) * X i j = ∑ j, X k j := by
            simp [Finset.sum_ite_eq]
          have hX : ∀ i j, X i j = φ i j * ∑ x ∈ states n m, π x * q x i j := by
            intro i j; simp only [X, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          have : ∑ i, X i k = ∑ j, X k j := by linarith
          simpa only [hX] using this
        have hjensen : ∀ (I : Fin n → Fin n → ℝ → ℝ),
            (∀ i j, ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (rewardCurve I i j)) →
            ∀ q π, IsPolicy n m q → IsStationary n m φ q π →
            obj n m φ I q π ≤ elevObj φ I (fun i j => ∑ x ∈ states n m, π x * q x i j) := by
          intro I hI q π hq hπ
          unfold obj elevObj
          calc ∑ x ∈ states n m, π x * ∑ i, ∑ j, φ i j * rewardCurve I i j (q x i j)
              = ∑ i, ∑ j, φ i j * ∑ x ∈ states n m, π x • rewardCurve I i j (q x i j) := by
                simp_rw [Finset.mul_sum, smul_eq_mul]; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_comm]
                exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun x _ => by ring))
            _ ≤ ∑ i, ∑ j, φ i j * rewardCurve I i j (∑ x ∈ states n m, π x * q x i j) := by
                gcongr with i _ j _
                · exact hφ i j
                · have := (hI i j).le_map_sum (t := states n m) (w := π) (p := fun x => q x i j)
                    (fun x _ => hπ.1 x) hπ.2.2.1
                    (fun x hx => ⟨(hq x hx i j).1, (hq x hx i j).2.1⟩)
                  simpa [smul_eq_mul] using this
        have hqt01 : ∀ i j, 0 ≤ qt i j ∧ qt i j ≤ 1 := hopt.1.1.1
        have hqbal : IsBalanced φ qt := hopt.1.1.2
        have hB : ∀ I : Fin n → Fin n → ℝ → ℝ,
            obj n m φ I (toPolicy qt) πt = (m : ℝ) / ((m : ℝ) + n - 1) * elevObj φ I qt := by
          intro I
          rcases hconn with hsc | h0
          swap
          · subst h0
            simp [obj, elevObj, toPolicy, rewardCurve]
          obtain _ | m' := m
          · simp only [CharP.cast_eq_zero, zero_div, zero_mul]
            apply Finset.sum_eq_zero
            intro x hx
            have hx0 : ∀ i, x i = 0 := by
              intro i
              have := (hmem x).1 hx
              exact (Finset.sum_eq_zero_iff.1 this) i (Finset.mem_univ _)
            simp [toPolicy, hx0, rewardCurve]
          obtain ⟨h0π, hoff, h1π, hbal⟩ := hπt
          have hne : (states n (m' + 1)).Nonempty := by
            by_contra h
            rw [Finset.not_nonempty_iff_eq_empty] at h
            rw [h, Finset.sum_empty] at h1π; exact zero_ne_one h1π
          obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image _ πt hne
          set M := πt x0 with hMdef
          have hM_all : ∀ y, πt y ≤ M := by
            intro y
            by_cases hy : y ∈ states n (m' + 1)
            · exact hmax y hy
            · rw [hoff y hy]; exact h0π x0
          have hMpos : 0 < M := by
            by_contra hcon
            push_neg at hcon
            have : ∑ x ∈ states n (m' + 1), πt x ≤ ∑ x ∈ states n (m' + 1), (0:ℝ) :=
              Finset.sum_le_sum (fun x _ => le_trans (hM_all x) hcon)
            simp at this; linarith
          have hinS : ∀ y, πt y = M → y ∈ states n (m' + 1) := by
            intro y hy
            by_contra h
            rw [hoff y h] at hy; linarith
          have step1 : ∀ x i j, πt x = M → i ≠ j → 0 < φ i j * qt i j → 1 ≤ x j →
              πt (moveState x i j) = M := by
            intro x i j hx hij hpos hj
            have hb := hbal x (hinS x hx)
            let u : Fin n → Fin n → ℝ := fun a b => if 1 ≤ x b then φ a b * qt a b else 0
            have hle : ∀ a b, inflowTerm φ (toPolicy qt) πt x a b ≤ M * u a b := by
              intro a b
              simp only [inflowTerm, toPolicy, u]
              by_cases hab : a = b
              · subst hab
                simp only [if_true]
                rw [hx]
                by_cases h1 : 1 ≤ x a
                · have h2 : 0 < x a := h1
                  rw [if_pos h2, if_pos h1]; apply le_of_eq; ring
                · have h2 : ¬ 0 < x a := by omega
                  rw [if_neg h2, if_neg h1]; simp
              · rw [if_neg hab]
                by_cases h1 : 1 ≤ x b
                · rw [if_pos h1, if_pos h1]
                  have h2 : 0 < moveState x a b a := by rw [hmove_i x a b hab]; omega
                  rw [if_pos h2]
                  have := mul_nonneg (hφ a b) (hqt01 a b).1
                  nlinarith [hM_all (moveState x a b)]
                · rw [if_neg h1, if_neg h1]; simp
            have hsumu : ∑ a, ∑ b, u a b = ∑ a, ∑ b, φ a b * toPolicy qt x a b := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b _
              simp only [u, toPolicy]
              by_cases hb1 : 1 ≤ x b
              · have : 0 < x b := hb1
                simp only [hb1, this, if_true]; exact hqbal b
              · have : ¬ 0 < x b := by omega
                simp [hb1, this]
            have hzero : ∑ a, ∑ b, (M * u a b - inflowTerm φ (toPolicy qt) πt x a b) = 0 := by
              simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumu, ← hb, hx]; ring
            have hij0 : M * u i j - inflowTerm φ (toPolicy qt) πt x i j = 0 := by
              have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg
                (fun b _ => sub_nonneg.2 (hle a b)))).1 hzero i (Finset.mem_univ _)
              exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sub_nonneg.2 (hle i b))).1 h1 j
                (Finset.mem_univ _)
            have h2 : 0 < moveState x i j i := by rw [hmove_i x i j hij]; omega
            simp only [u, inflowTerm, toPolicy, hij, if_false, hj, if_true, h2] at hij0
            have h3 : (M - πt (moveState x i j)) * (φ i j * qt i j) = 0 := by linear_combination hij0
            rcases mul_eq_zero.1 h3 with h | h
            · linarith
            · linarith
          have step2 : ∀ a b, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < φ a b * qt a b) a b →
              ∀ x z : Fin n → ℕ, πt x = M → 1 ≤ x b → z + Pi.single b 1 = x + Pi.single a 1 →
                πt z = M := by
            intro a b hab
            induction hab with
            | refl =>
              intro x z hx _ hz
              rw [add_right_cancel hz]; exact hx
            | tail hau hub ih =>
              rename_i u b
              intro x z hx hb hz
              have hy := step1 x u b hx hub.1 hub.2 hb
              apply ih (moveState x u b) z hy (by rw [hmove_i x u b hub.1]; omega)
              funext k
              have h1 := congrFun hz k
              simp only [Pi.add_apply, Pi.single_apply, moveState, Function.update_apply] at h1 ⊢
              by_cases hku : k = u
              · subst hku
                have : k ≠ b := hub.1
                simp only [this, if_false, if_true] at h1 ⊢
                omega
              · by_cases hkb : k = b
                · subst hkb
                  simp only [hku, if_false, if_true] at h1 ⊢
                  omega
                · simp only [hku, hkb, if_false] at h1 ⊢
                  omega
          have step3 : ∀ z ∈ states n (m' + 1), πt z = M := by
            intro z hz
            have hzs := (hmem z).1 hz
            suffices H : ∀ N x, πt x = M → ∑ k, (x k - z k) = N → πt z = M from H _ x0 rfl rfl
            intro N
            induction N with
            | zero =>
              intro x hx hN
              have hxs := (hmem x).1 (hinS x hx)
              have hle : ∀ k, x k ≤ z k := fun k => by
                have := (Finset.sum_eq_zero_iff.1 hN) k (Finset.mem_univ _); omega
              have heq := (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).1 (by rw [hxs, hzs])
              have : x = z := funext (fun k => heq k (Finset.mem_univ _))
              rw [← this]; exact hx
            | succ N ih =>
              intro x hx hN
              have hxs := (hmem x).1 (hinS x hx)
              obtain ⟨a, ha⟩ : ∃ a, z a < x a := by
                by_contra hcon
                push_neg at hcon
                have : ∑ k, (x k - z k) = 0 :=
                  Finset.sum_eq_zero (fun k _ => by have := hcon k; omega)
                omega
              obtain ⟨b, hb⟩ : ∃ b, x b < z b := by
                by_contra hcon
                push_neg at hcon
                have h := (Finset.sum_eq_sum_iff_of_le (fun k _ => hcon k)).1 (by rw [hxs, hzs])
                have := h a (Finset.mem_univ _); omega
              have hab : a ≠ b := by rintro rfl; omega
              let z' : Fin n → ℕ := fun k => if k = a then x a - 1 else if k = b then x b + 1 else x k
              have hz' : πt z' = M := by
                apply step2 b a (hsc b a) x z' hx (by omega)
                funext k
                simp only [z', Pi.add_apply, Pi.single_apply]
                by_cases hka : k = a
                · subst hka; simp [hab]; omega
                · by_cases hkb : k = b
                  · subst hkb; simp [hka]
                  · simp [hka, hkb]
              apply ih z' hz'
              have e : ∀ k, (z' k - z k) + (if k = a then 1 else 0) = x k - z k := by
                intro k; simp only [z']
                by_cases hka : k = a
                · subst hka; simp; omega
                · by_cases hkb : k = b
                  · subst hkb; simp [hka]; omega
                  · simp [hka, hkb]
              have : ∑ k, (z' k - z k) + 1 = ∑ k, (x k - z k) := by
                rw [← Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib,
                  Finset.sum_ite_eq']
                simp
              omega
          have hcard : ((states n (m' + 1)).card : ℝ) * M = 1 := by
            rw [← h1π, Finset.sum_congr rfl step3]; simp
          have hshift : ∀ i (g : (Fin n → ℕ) → ℝ), ∑ y ∈ states n m', g (y + Pi.single i 1) =
              ∑ x ∈ (states n (m' + 1)).filter (fun x => 1 ≤ x i), g x := by
            intro i g
            apply Finset.sum_nbij' (fun y => y + Pi.single i 1) (fun x => x - Pi.single i 1)
            · intro y hy
              simp only [Finset.mem_filter, hmem] at hy ⊢
              simp [Finset.sum_add_distrib, hy]
            · intro x hx
              simp only [Finset.mem_filter, hmem] at hx ⊢
              have e : (x - Pi.single i 1) + Pi.single i 1 = x := by
                funext k; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
                split_ifs with h
                · subst h; omega
                · omega
              have := congrArg (fun f : Fin n → ℕ => ∑ k, f k) e
              simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
                if_true] at this
              omega
            · intro y _; funext k; simp
            · intro x hx
              simp only [Finset.mem_filter] at hx
              funext k; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
              split_ifs with h
              · subst h; omega
              · omega
            · intro y _; rfl
          have hU : ∀ i, ((states n (m' + 1)).filter (fun x => 1 ≤ x i)).card =
              (states n m').card := by
            intro i
            have := hshift i (fun _ => 1)
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj] at this
            exact this.symm
          have hW : ∀ i, ∑ y ∈ states n m', ((y i : ℝ) + 1) =
              ∑ x ∈ states n (m' + 1), (x i : ℝ) := by
            intro i
            have := hshift i (fun x => (x i : ℝ))
            simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one] at this
            rw [this, Finset.sum_filter]
            apply Finset.sum_congr rfl; intro x _
            split_ifs with h
            · rfl
            · have : x i = 0 := by omega
              simp [this]
          have hTT : ((states n m').card : ℝ) * ((m' : ℝ) + n) =
              ((states n (m' + 1)).card : ℝ) * ((m' : ℝ) + 1) := by
            have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hW i)
            rw [Finset.sum_comm, Finset.sum_comm (t := states n (m' + 1))] at h
            have l : ∑ y ∈ states n m', ∑ i, ((y i : ℝ) + 1) =
                ∑ y ∈ states n m', ((m' : ℝ) + n) := by
              apply Finset.sum_congr rfl; intro y hy
              rw [Finset.sum_add_distrib, ← Nat.cast_sum, (hmem y).1 hy]; simp
            have r : ∑ x ∈ states n (m' + 1), ∑ i, (x i : ℝ) =
                ∑ x ∈ states n (m' + 1), ((m' : ℝ) + 1) := by
              apply Finset.sum_congr rfl; intro x hx
              rw [← Nat.cast_sum, (hmem x).1 hx]; push_cast; ring
            rw [l, r] at h
            simp only [Finset.sum_const, nsmul_eq_mul] at h; linarith
          have hobj : obj n (m' + 1) φ I (toPolicy qt) πt =
              M * ((states n m').card : ℝ) * elevObj φ I qt := by
            unfold obj elevObj
            calc ∑ x ∈ states n (m' + 1), πt x * ∑ i, ∑ j, φ i j * rewardCurve I i j (toPolicy qt x i j)
                = ∑ x ∈ states n (m' + 1), ∑ i, ∑ j,
                    M * (if 1 ≤ x i then φ i j * rewardCurve I i j (qt i j) else 0) := by
                  apply Finset.sum_congr rfl; intro x hx
                  rw [step3 x hx, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
                  simp only [toPolicy]
                  by_cases h : 1 ≤ x i
                  · have h' : 0 < x i := h
                    rw [if_pos h', if_pos h]
                  · have h' : ¬ 0 < x i := by omega
                    rw [if_neg h', if_neg h]; simp [rewardCurve]
              _ = ∑ i, ∑ j, M * ∑ x ∈ states n (m' + 1),
                    (if 1 ≤ x i then φ i j * rewardCurve I i j (qt i j) else 0) := by
                  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
                  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
                  rw [Finset.mul_sum]
              _ = ∑ i, ∑ j, M * (((states n m').card : ℝ) * (φ i j * rewardCurve I i j (qt i j))) := by
                  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
                  rw [← Finset.sum_filter, Finset.sum_const, hU i, nsmul_eq_mul]
              _ = M * ((states n m').card : ℝ) * ∑ i, ∑ j, φ i j * rewardCurve I i j (qt i j) := by
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
          rw [hobj]
          congr 1
          have hTpos : ((states n (m' + 1)).card : ℝ) ≠ 0 := by
            intro h; rw [h] at hcard; simp at hcard
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
          have hden : ((m' + 1 : ℕ) : ℝ) + n - 1 ≠ 0 := by
            push_cast
            intro h
            have e1 : (n : ℝ) = 0 := by linarith
            have e2 : (m' : ℝ) = 0 := by linarith
            apply hTpos
            rw [e1, e2] at hTT
            linarith
          rw [eq_div_iff hden]
          push_cast
          have e : (m' : ℝ) + 1 + n - 1 = m' + n := by ring
          rw [e]
          calc M * ((states n m').card : ℝ) * (m' + n)
              = M * (((states n (m' + 1)).card : ℝ) * (m' + 1)) := by rw [mul_assoc, hTT]
            _ = (((states n (m' + 1)).card : ℝ) * M) * (m' + 1) := by ring
            _ = m' + 1 := by rw [hcard]; ring
        have hγ : 0 ≤ (m : ℝ) / ((m : ℝ) + n - 1) := by
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; simp
          · apply div_nonneg (Nat.cast_nonneg m)
            have : (1 : ℝ) ≤ m := by exact_mod_cast hm
            have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith
        refine ⟨fun q π hq hπ hcq => ?_, ?_⟩
        · have hfeas : IsAlg5Feasible φ IΨ c (fun i j => ∑ x ∈ states n m, π x * q x i j) := by
            refine ⟨⟨fun i j => ⟨?_, ?_⟩, fun k => hflow q π hq hπ k⟩,
              le_trans hcq (hjensen IΨ hΨ q π hq hπ)⟩
            · exact Finset.sum_nonneg (fun x hx => mul_nonneg (hπ.1 x) (hq x hx i j).1)
            · calc ∑ x ∈ states n m, π x * q x i j ≤ ∑ x ∈ states n m, π x * 1 :=
                    Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hq x hx i j).2.1 (hπ.1 x))
                _ = 1 := by simp [hπ.2.2.1]
          have := hopt.2 _ hfeas
          rw [hB IΦ]
          exact mul_le_mul_of_nonneg_left (le_trans (hjensen IΦ hΦ q π hq hπ) this) hγ
        · rw [hB IΨ]; exact mul_le_mul_of_nonneg_left hopt.1.2 hγ
