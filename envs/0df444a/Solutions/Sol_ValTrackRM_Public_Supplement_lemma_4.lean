-- Prove2me | solution 1 for ValTrackRM.Public.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:07.327075+00:00
-- url     : https://prove2.me/submissions/8ab16913-1109-4ba7-bc8f-73eba2168f66

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Stochastic

open ValTrackRM
open ValTrackRM.Public
open ValTrackRM.Public.Supplement
set_option maxHeartbeats 0

theorem solution
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) :
    (∀ (t : ℕ), 1 ≤ t → t ≤ T → ∀ (a : Fin (k + 1)),
      0 < stochasticStock r k (expKernel r sel ν) ν (t - 1) a.val → ∀ p : Price m,
      stochasticConditional r k (expKernel r sel ν) ν t a.val p =
        jointA1Price r sel ν (t - 1) a.val p / jointA1Stock r sel ν (t - 1) a.val) ∧
    (∀ (t : ℕ), t ≤ T → ∀ a : Fin (k + 1),
      stochasticStock r k (expKernel r sel ν) ν t a.val = jointA1Stock r sel ν t a.val) := by
        -- strict monotonicity of r on [0, m]
        have hrmono : ∀ a b : ℕ, a < b → b ≤ m → r a < r b := by
          intro a b hab hbm
          induction b with
          | zero => omega
          | succ b ih =>
            rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
            · exact lt_trans (ih h (by omega)) (hr b (by omega))
            · subst h; exact hr a (by omega)
        have hrpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < r j := by
          intro j hj1 hjm
          have := hrmono 0 j (by omega) hjm
          rwa [hr0] at this
        have hrnonneg : ∀ j : ℕ, j ≤ m → 0 ≤ r j := by
          intro j hjm
          rcases Nat.eq_zero_or_pos j with h | h
          · subst h; rw [hr0]
          · exact le_of_lt (hrpos j h hjm)
        have hqj_nonneg : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 ≤ qj r j := by
          intro j hj1 hjm
          unfold qj
          have h1 := hrpos j hj1 hjm
          have h2 := hrnonneg (j - 1) (by omega)
          have h3 : r (j - 1) < r j := hrmono (j - 1) j (by omega) hjm
          rw [sub_nonneg, div_le_one h1]; exact le_of_lt h3
        have hqj_mul : ∀ j : ℕ, 1 ≤ j → j ≤ m → qj r j * r j = r j - r (j - 1) := by
          intro j hj1 hjm
          unfold qj
          have h1 := hrpos j hj1 hjm
          field_simp
        have hqTot_pos : ∀ ℓ : ℕ, ℓ < m → 0 < qTot r m ℓ := by
          intro ℓ hℓ
          unfold qTot
          have hmpos : 0 < qj r m := by
            unfold qj
            have h1 := hrpos m hm le_rfl
            have h3 : r (m - 1) < r m := hrmono (m - 1) m (by omega) le_rfl
            rw [sub_pos, div_lt_one h1]; exact h3
          calc (0:ℝ) < qj r m := hmpos
            _ ≤ ∑ p ∈ Finset.Ioc ℓ m, qj r p := by
              apply Finset.single_le_sum (f := fun p => qj r p)
              · intro p hp; simp only [Finset.mem_Ioc] at hp; exact hqj_nonneg p (by omega) hp.2
              · simp only [Finset.mem_Ioc]; omega
        have hlevSnoc : ∀ (V : List (Fin (m + 1))) (v : Fin (m + 1)),
            levels sel (V ++ [v]) = levelStep sel (levels sel V) v := by
          intro V v
          unfold levels
          rw [List.foldl_append]
          rfl
        have hsoldSnoc : ∀ (V : List (Fin (m + 1))) (v : Fin (m + 1)),
            soldLaw r sel (V ++ [v]) = lawStep r sel (levels sel V) v (soldLaw r sel V) := by
          intro V v
          unfold soldLaw
          rw [List.reverse_append]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
          rw [soldLawRev, List.reverse_reverse]
        -- pushforward of a function through one Algorithm 1 step
        have hG : ∀ (L : Fin k → Fin (m + 1)) (v : Fin (m + 1)) (μ : (Fin k → Bool) → ℝ)
            (φ : (Fin k → Bool) → ℝ),
            ∑ s', lawStep r sel L v μ s' * φ s' =
              ∑ s, μ s * (if s (sel L) = false ∧ ((L (sel L) : ℕ) < m) then
                ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
                  (if r p ≤ r v then φ (Function.update s (sel L) true) else φ s)
                else φ s) := by
          intro L v μ φ
          unfold lawStep
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          simp_rw [mul_assoc, ← Finset.mul_sum]
          congr 1
          split_ifs with hc
          · simp_rw [Finset.sum_mul, mul_assoc]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            split_ifs <;> simp
          · simp
        -- Block B: OPT equals the sum of the levels
        have hOP : ∀ ℓ p : ℕ, ℓ < m → p ∈ Finset.Ioc ℓ m → 0 ≤ offerProb r m ℓ p := by
          intro ℓ p hℓ hp
          simp only [Finset.mem_Ioc] at hp
          exact div_nonneg (hqj_nonneg p (by omega) hp.2) (hqTot_pos ℓ hℓ).le
        have hSoldNN : ∀ V s, 0 ≤ soldLaw r sel V s := by
          intro V
          unfold soldLaw
          generalize V.reverse = R
          induction R with
          | nil => intro s; simp only [soldLawRev]; split_ifs <;> norm_num
          | cons j R ih =>
            intro s'
            rw [soldLawRev]
            unfold lawStep
            apply Finset.sum_nonneg
            intro s _
            apply mul_nonneg (ih s)
            by_cases hc : s (sel (levels sel R.reverse)) = false ∧
                ((levels sel R.reverse (sel (levels sel R.reverse)) : ℕ) < m)
            · rw [if_pos hc]
              apply Finset.sum_nonneg
              intro p hp
              apply mul_nonneg (hOP _ p hc.2 hp)
              split_ifs <;> norm_num
            · rw [if_neg hc]
              split_ifs <;> norm_num
        have hWNN : ∀ n (W : Fin n → Fin (m + 1)), 0 ≤ valuationWeight ν W := by
          intro n W
          exact Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
        have hν1 : ∀ t, ∑ v : Fin (m + 1), (ν t v).toReal = 1 := by
          intro t
          have h1 := (ν t).tsum_coe
          rw [tsum_fintype] at h1
          rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _), h1, ENNReal.toReal_one]
        have hinvle : ∀ s : Fin k → Bool, inventory s ≤ k := by
          intro s
          unfold inventory
          exact (Finset.card_filter_le _ _).trans (by simp)
        have hinvpos : ∀ (s : Fin k → Bool) (i : Fin k), s i = false → 0 < inventory s := by
          intro s i hi
          unfold inventory
          exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
        have hinvupd : ∀ (s : Fin k → Bool) (i : Fin k), s i = false →
            inventory (Function.update s i true) = inventory s - 1 := by
          intro s i hi
          unfold inventory
          have : (Finset.univ.filter fun j => Function.update s i true j = false) =
              (Finset.univ.filter fun j => s j = false).erase i := by
            ext j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj, hj]
          rw [this, Finset.card_erase_of_mem (by simp [hi])]
        have hinv0 : ∀ (s : Fin k → Bool) (i : Fin k), inventory s = 0 → s i = true := by
          intro s i hs
          by_contra hc
          have := hinvpos s i (by simpa using hc)
          omega
        have hRI : ∀ (ℓ : ℕ) (f : ℕ → ℝ), ∑ p : Fin (m + 1),
            (if ℓ < p.val + 1 ∧ p.val < m then f (p.val + 1) else 0) = ∑ p ∈ Finset.Ioc ℓ m, f p := by
          intro ℓ f
          rw [Fin.sum_univ_eq_sum_range (fun p => if ℓ < p + 1 ∧ p < m then f (p + 1) else 0),
            ← Finset.sum_filter]
          symm
          apply Finset.sum_nbij' (fun p => p - 1) (fun p => p + 1)
          · intro a ha; simp at ha ⊢; try omega
          · intro a ha; simp at ha ⊢; try omega
          · intro a ha; simp at ha ⊢; try omega
          · intro a ha; simp at ha ⊢; try omega
          · intro a ha; simp only [Finset.mem_Ioc] at ha; congr 1; omega
        have hT1 : ∀ (L : Fin k → Fin (m + 1)) (s : Fin k → Bool) (v : Fin (m + 1)) (b : ℕ),
            ∑ p : Price m, unitPrice r sel L s p *
                (if nextStock r (inventory s) p v = b then (1:ℝ) else 0) =
              (if s (sel L) = false ∧ ((L (sel L) : ℕ) < m) then
                ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
                  (if r p ≤ r v then (if inventory (Function.update s (sel L) true) = b then (1:ℝ) else 0)
                    else (if inventory s = b then (1:ℝ) else 0))
              else (if inventory s = b then (1:ℝ) else 0)) := by
          intro L s v b
          by_cases h : s (sel L) = false ∧ ((L (sel L) : ℕ) < m)
          · rw [if_pos h, ← hRI]
            refine Finset.sum_congr rfl fun p _ => ?_
            have hpos := hinvpos s _ h.1
            have hupd := hinvupd s _ h.1
            rw [unitPrice, if_pos h]
            by_cases hc : (L (sel L) : ℕ) < p.val + 1 ∧ p.val < m
            · rw [if_pos hc, if_pos hc]
              congr 1
              by_cases hrv : r (p.val + 1) ≤ r v
              · rw [if_pos hrv, hupd]
                simp [nextStock, buys, hpos, hc.2, hrv]
              · rw [if_neg hrv]
                simp [nextStock, buys, hrv]
            · rw [if_neg hc, if_neg hc, zero_mul]
          · rw [if_neg h, Finset.sum_eq_single (Fin.last m)]
            · simp [unitPrice, h, reject, nextStock, buys]
            · intro p _ hp
              have : p.val ≠ m := fun h' => hp (Fin.ext (by simp [h']))
              simp [unitPrice, h, reject, this]
            · simp
        have hT2 : ∀ (L : Fin k → Fin (m + 1)) (s : Fin k → Bool) (v : Fin (m + 1)),
            ∑ p : Price m, unitPrice r sel L s p * payment r (inventory s) p v =
              (if s (sel L) = false ∧ ((L (sel L) : ℕ) < m) then
                ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
                  (if r p ≤ r v then r p else 0)
              else 0) := by
          intro L s v
          by_cases h : s (sel L) = false ∧ ((L (sel L) : ℕ) < m)
          · rw [if_pos h, ← hRI]
            refine Finset.sum_congr rfl fun p _ => ?_
            have hpos := hinvpos s _ h.1
            rw [unitPrice, if_pos h]
            by_cases hc : (L (sel L) : ℕ) < p.val + 1 ∧ p.val < m
            · rw [if_pos hc, if_pos hc]
              congr 1
              by_cases hrv : r (p.val + 1) ≤ r v
              · rw [if_pos hrv]; simp [payment, buys, hpos, hc.2, hrv]
              · rw [if_neg hrv]; simp [payment, buys, hrv]
            · rw [if_neg hc, if_neg hc, zero_mul]
          · rw [if_neg h]
            apply Finset.sum_eq_zero
            intro p _
            by_cases hp : p.val = m
            · simp [payment, buys, hp]
            · simp [unitPrice, h, reject, hp]
        have hA1snoc : ∀ (V : List (Fin (m + 1))) (v : Fin (m + 1)) (b : ℕ),
            a1Stock r sel (V ++ [v]) b = ∑ s, soldLaw r sel V s *
              ∑ p, unitPrice r sel (levels sel V) s p *
                (if nextStock r (inventory s) p v = b then (1:ℝ) else 0) := by
          intro V v b
          unfold a1Stock
          rw [hsoldSnoc, hG (levels sel V) v (soldLaw r sel V) (fun s => if inventory s = b then (1:ℝ) else 0)]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hT1]
        have hSN : ∀ (n : ℕ) (g : List (Fin (m + 1)) → ℝ),
            ∑ W' : Fin (n + 1) → Fin (m + 1), valuationWeight ν W' * g (List.ofFn W') =
              ∑ W : Fin n → Fin (m + 1), ∑ v, valuationWeight ν W * (ν (n + 1) v).toReal *
                g (List.ofFn W ++ [v]) := by
          intro n g
          rw [← (Fin.snocEquiv (fun _ => Fin (m + 1))).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun v _ => ?_
          congr 1
          · unfold valuationWeight
            rw [Fin.prod_univ_castSucc]
            simp
          · congr 1
            rw [List.ofFn_succ', List.concat_eq_append]
            simp
        have hcol : ∀ (s : Fin k → Bool) (y : ℝ),
            ∑ a : Fin (k + 1), (if inventory s = (a : ℕ) then y else 0) = y := by
          intro s y
          rw [Finset.sum_eq_single (⟨inventory s, Nat.lt_succ_of_le (hinvle s)⟩ : Fin (k + 1))]
          · simp
          · intro a _ ha
            rw [if_neg]
            intro h; apply ha; ext; simp [h]
          · simp
        have hShuf : ∀ (n : ℕ) (c : Fin (m + 1) → ℝ) (h : ℕ → Price m → Fin (m + 1) → ℝ),
            ∑ a : Fin (k + 1), ∑ p : Price m, ∑ v : Fin (m + 1),
                jointA1Price r sel ν n a p * c v * h a p v =
              ∑ W : Fin n → Fin (m + 1), ∑ v, valuationWeight ν W * c v *
                ∑ s, soldLaw r sel (List.ofFn W) s *
                  ∑ p, unitPrice r sel (levels sel (List.ofFn W)) s p * h (inventory s) p v := by
          intro n c h
          have e : ∀ (a : Fin (k + 1)) (p : Price m) (v : Fin (m + 1)),
              jointA1Price r sel ν n a p * c v * h a p v =
                ∑ W : Fin n → Fin (m + 1), ∑ s, (if inventory s = (a : ℕ) then
                  valuationWeight ν W * c v * (soldLaw r sel (List.ofFn W) s *
                    (unitPrice r sel (levels sel (List.ofFn W)) s p * h (inventory s) p v)) else 0) := by
            intro a p v
            unfold jointA1Price a1Joint
            rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun W _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => ?_
            split_ifs with hs
            · rw [hs]; ring
            · ring
          simp only [e]
          rw [Finset.sum_comm]
          conv_lhs => enter [2, p]; rw [Finset.sum_comm]
          conv_lhs => enter [2, p, 2, v]; rw [Finset.sum_comm]
          conv_lhs => enter [2, p, 2, v, 2, W]; rw [Finset.sum_comm]
          simp only [hcol]
          rw [Finset.sum_comm]
          conv_lhs => enter [2, v]; rw [Finset.sum_comm]
          conv_lhs => enter [2, v, 2, W]; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
        have hJ0 : ∀ n (a : ℕ) (p : Price m), jointA1Stock r sel ν n a = 0 →
            jointA1Price r sel ν n a p = 0 := by
          intro n a p hJ
          have hind : ∀ s : Fin k → Bool, (0:ℝ) ≤ if inventory s = a then 1 else 0 := by
            intro s; split_ifs <;> norm_num
          have hA1NN : ∀ V : List (Fin (m + 1)), 0 ≤ a1Stock r sel V a := fun V =>
            Finset.sum_nonneg fun s _ => mul_nonneg (hSoldNN _ s) (hind s)
          unfold jointA1Stock at hJ
          have hJ' := (Finset.sum_eq_zero_iff_of_nonneg (fun W _ => mul_nonneg (hWNN n W)
            (hA1NN (List.ofFn W)))).mp hJ
          unfold jointA1Price
          apply Finset.sum_eq_zero
          intro W _
          rcases mul_eq_zero.mp (hJ' W (Finset.mem_univ _)) with hw | hA
          · rw [hw, zero_mul]
          · unfold a1Stock at hA
            have hA' := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hSoldNN _ s)
              (hind s))).mp hA
            unfold a1Joint
            rw [Finset.sum_eq_zero, mul_zero]
            intro s _
            have := hA' s (Finset.mem_univ _)
            by_cases hs : inventory s = a
            · simp only [hs, if_true, mul_one] at this; rw [this, zero_mul]
            · rw [if_neg hs, mul_zero]
        have hKey : ∀ n (a : ℕ) (p : Price m),
            stochasticStock r k (expKernel r sel ν) ν n a = jointA1Stock r sel ν n a →
            stochasticStock r k (expKernel r sel ν) ν n a * expKernel r sel ν (n + 1) a p =
              jointA1Price r sel ν n a p := by
          intro n a p hS
          rw [hS]
          unfold expKernel
          simp only [Nat.add_sub_cancel]
          split_ifs with h
          · rcases h with h0 | hJ
            · subst h0
              unfold jointA1Stock jointA1Price
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun W _ => ?_
              unfold a1Stock a1Joint
              rw [mul_assoc, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun s _ => ?_
              by_cases hs : inventory s = 0
              · rw [if_pos hs, if_pos hs, unitPrice, if_neg]
                · ring
                · intro hc; rw [hinv0 s _ hs] at hc; exact Bool.noConfusion hc.1
              · rw [if_neg hs, if_neg hs]; ring
            · rw [hJ, zero_mul, hJ0 n a p hJ]
          · have hne : jointA1Stock r sel ν n a ≠ 0 := (not_or.mp h).2
            field_simp
        have hStock : ∀ n (b : ℕ), b ≤ k →
            stochasticStock r k (expKernel r sel ν) ν n b = jointA1Stock r sel ν n b := by
          intro n
          induction n with
          | zero =>
            intro b hb
            simp only [stochasticStock, jointA1Stock]
            rw [Fintype.sum_unique]
            simp only [valuationWeight, Finset.univ_eq_empty, Finset.prod_empty, one_mul, List.ofFn_zero,
              a1Stock, soldLaw, List.reverse_nil, soldLawRev]
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            have : inventory (fun _ : Fin k => false) = k := by simp [inventory]
            rw [this]
            by_cases hbk : b = k
            · simp [hbk]
            · rw [if_neg hbk, if_neg (Ne.symm hbk)]
          | succ n ih =>
            intro b hb
            rw [stochasticStock]
            have e1 : ∀ (a : Fin (k + 1)) (p : Price m),
                stochasticStock r k (expKernel r sel ν) ν n a * expKernel r sel ν (n + 1) a p =
                  jointA1Price r sel ν n a p := fun a p => hKey n a p (ih a (by omega))
            simp only [e1]
            have := hShuf n (fun v => (ν (n + 1) v).toReal)
              (fun a p v => if nextStock r a p v = b then (1:ℝ) else 0)
            rw [this]
            unfold jointA1Stock
            rw [hSN n (fun V => a1Stock r sel V b)]
            refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun v _ => ?_
            rw [hA1snoc]
        refine ⟨?_, fun t _ a => hStock t a (Nat.lt_succ_iff.mp a.isLt)⟩
        intro t ht _ a hpos p
        obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
        unfold stochasticConditional
        simp only [Nat.add_sub_cancel] at hpos ⊢
        rw [hKey n a p (hStock n a (Nat.lt_succ_iff.mp a.isLt)), hStock n a (Nat.lt_succ_iff.mp a.isLt)]
