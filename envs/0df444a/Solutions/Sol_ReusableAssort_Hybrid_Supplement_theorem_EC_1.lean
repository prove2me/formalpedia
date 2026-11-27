-- Prove2me | solution 1 for ReusableAssort.Hybrid.Supplement.theorem_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:55.264809+00:00
-- url     : https://prove2.me/submissions/56965f2c-8453-4e29-bffa-d28bc671f76e

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Offline

open ReusableAssort
open ReusableAssort.Hybrid
open ReusableAssort.Hybrid.Supplement

theorem solution (T : ℕ) (hT : 1 ≤ T) :
    ∃ (n m : ℕ) (I : Instance n T (Fin m)), I.Assumptions ∧
      (∃ y, LPFeasible I y ∧ 0 < lpObj I y) ∧
      (∀ y, LPFeasible I y → lpObj I y ≤ 2) ∧
      ∀ law, ValidChoiceLaw I law → (T : ℝ) / 2 ≤ optOffline I law ∧
        ∀ y, LPFeasible I y → lpObj I y ≤ (4 / (T : ℝ)) * optOffline I law := by
          classical
          obtain ⟨I, hc, hfeas, hphi, hr, hg, hF⟩ : ∃ I : Instance 1 T (Fin 1),
              (∀ i, I.c i = 1) ∧ I.feas = Finset.univ ∧
              (∀ z S i, I.phi z S i = if i ∈ S then 1 else 0) ∧ (∀ z i, I.r z i = 1) ∧
              (∀ z i d, I.g z i d = (if d = 1 then (1/2 : ℝ) else 0) + (if d = T then (1/2 : ℝ) else 0)) ∧
              (∀ t z, I.F t z = 1) :=
            ⟨{ c := fun _ => 1
               feas := Finset.univ
               phi := fun _ S i => if i ∈ S then 1 else 0
               r := fun _ _ => 1
               g := fun _ _ d => (if d = 1 then (1/2 : ℝ) else 0) + (if d = T then (1/2 : ℝ) else 0)
               F := fun _ _ => 1 }, fun _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl,
               fun _ _ _ => rfl, fun _ _ => rfl⟩
          have hgnn : ∀ z i d, 0 ≤ I.g z i d := by
            intro z i d
            rw [hg]
            split_ifs <;> norm_num
          have hgsum : ∀ z i, ∑ d ∈ Finset.Icc 1 T, I.g z i d = 1 := by
            intro z i
            simp only [hg]
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
            rw [if_pos (Finset.mem_Icc.2 ⟨le_refl 1, hT⟩), if_pos (Finset.mem_Icc.2 ⟨hT, le_refl T⟩)]
            norm_num
          have hg0 : ∀ z i, I.g z i 0 = 0 := by
            intro z i
            rw [hg, if_neg (by omega), if_neg (by omega)]
            norm_num
          have hA : I.Assumptions := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgnn, hg0, ?_, hgsum, ?_, ?_⟩
            · intro z i
              simp [hphi]
            · intro z S _ i j hj _
              exact absurd (Subsingleton.elim j i) hj
            · rw [hfeas]; exact Finset.univ_nonempty
            · intro S _ S' _
              rw [hfeas]; exact Finset.mem_univ _
            · intro z S _ i
              rw [hphi]; split_ifs <;> norm_num
            · intro z S _ i hi
              rw [hphi, if_neg hi]
            · intro z S _
              simp only [hphi]
              calc ∑ i ∈ S, (if i ∈ S then (1:ℝ) else 0) ≤ ∑ i ∈ S, (1:ℝ) := by
                    apply Finset.sum_le_sum
                    intro i _
                    split_ifs <;> norm_num
                _ ≤ 1 := by
                    have := Finset.card_le_univ S
                    simp only [Fintype.card_fin] at this
                    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
                    exact_mod_cast this
            · intro z i; rw [hr]; norm_num
            · intro i; rw [hc]
            · intro z i d hd
              rw [hg, if_neg (by omega), if_neg (by omega)]
              norm_num
            · intro t z; rw [hF]; norm_num
            · intro t _
              simp [hF]
          have hGle : ∀ z i k, Gbar I z i k ≤ 1 := by
            intro z i k
            rw [← hgsum z i]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun d _ _ => hgnn z i d)
          have hGge : ∀ z i k, k < T → 1/2 ≤ Gbar I z i k := by
            intro z i k hk
            have h1 : I.g z i T ≤ Gbar I z i k :=
              Finset.single_le_sum (f := fun d => I.g z i d) (fun d _ => hgnn z i d)
                (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hT, le_refl T⟩, hk⟩)
            refine le_trans ?_ h1
            rw [hg, if_pos rfl]
            split_ifs <;> norm_num
          have hLP2 : ∀ y, LPFeasible I y → lpObj I y ≤ 2 := by
            intro y hy
            obtain ⟨hy0, hy1, -⟩ := hy
            have h1 := hy1 0 T (Finset.mem_Icc.2 ⟨hT, le_refl T⟩)
            rw [hc] at h1
            have h2 : (1/2 : ℝ) * lpObj I y ≤ ∑ τ ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas,
              I.F τ z * Gbar I z 0 (T - τ) * I.phi z S 0 * y τ z S := by
              unfold lpObj
              simp only [Finset.mul_sum]
              refine Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun z _ =>
                Finset.sum_le_sum fun S hS => ?_
              rw [Fin.sum_univ_one]
              have hG := hGge z 0 (T - τ) (by have := Finset.mem_Icc.1 hτ; omega)
              have hp := mul_nonneg (hA.phi_nonneg z S hS 0) (hy0 τ hτ z S hS)
              rw [hF, hr]
              nlinarith
            push_cast at h1
            linarith
          have hex : ∃ y, LPFeasible I y ∧ 0 < lpObj I y := by
            refine ⟨fun t _ S => if t = 1 then (if S = {0} then 1 else 0) else 0, ⟨?_, ?_, ?_⟩, ?_⟩
            · intro t _ z S _
              dsimp only
              split_ifs <;> norm_num
            · intro i t ht
              have h1t := (Finset.mem_Icc.1 ht).1
              have hcol : ∀ τ ∈ Finset.Icc 1 t, (∑ z, ∑ S ∈ I.feas, I.F τ z * Gbar I z i (t - τ) * I.phi z S i *
                  (if τ = 1 then (if S = {0} then (1:ℝ) else 0) else 0)) =
                  if τ = 1 then Gbar I 0 i (t - τ) else 0 := by
                intro τ _
                have hi : i = 0 := Subsingleton.elim _ _
                subst hi
                rw [Fin.sum_univ_one, hfeas]
                split_ifs with h
                · rw [Finset.sum_eq_single ({0} : Finset (Fin 1))]
                  · simp [hF, hphi]
                  · intro S _ hS
                    simp [hS]
                  · intro h; exact absurd (Finset.mem_univ _) h
                · simp
              dsimp only
              rw [Finset.sum_congr rfl hcol, Finset.sum_ite_eq',
                if_pos (Finset.mem_Icc.2 ⟨le_refl 1, h1t⟩), hc]
              push_cast
              exact hGle _ _ _
            · intro t _ z
              dsimp only
              rw [hfeas]
              split_ifs
              · simp
              · simp
            · unfold lpObj
              have hcol : ∀ τ ∈ Finset.Icc 1 T, (∑ z, ∑ S ∈ I.feas, ∑ i, I.F τ z * I.r z i * I.phi z S i *
                  (if τ = 1 then (if S = {0} then (1:ℝ) else 0) else 0)) =
                  if τ = 1 then 1 else 0 := by
                intro τ _
                rw [Fin.sum_univ_one, hfeas]
                split_ifs with h
                · rw [Finset.sum_eq_single ({0} : Finset (Fin 1))]
                  · simp [hF, hphi, hr]
                  · intro S _ hS
                    simp [hS]
                  · intro h; exact absurd (Finset.mem_univ _) h
                · simp
              rw [Finset.sum_congr rfl hcol, Finset.sum_ite_eq',
                if_pos (Finset.mem_Icc.2 ⟨le_refl 1, hT⟩)]
              norm_num
          have hopt : ∀ law, ValidChoiceLaw I law → (T : ℝ) / 2 ≤ optOffline I law := by
            intro law hlaw
            have hmem : ∀ k : Fin T, k.1 + 1 ∈ Finset.Icc 1 T := fun k =>
              Finset.mem_Icc.2 ⟨by omega, k.2⟩
            -- per-step weight
            let X := Fin 1 × (Fin 1 → Fin (T+1)) × (Finset (Fin 1) → Option (Fin 1))
            let w : Fin T → X → ℝ := fun k x =>
              I.F (k.1+1) x.1 * (∏ i, I.g x.1 i (x.2.1 i : ℕ)) * law (k.1+1) x.1 x.2.2
            let h : X → ℝ := fun x => if (x.2.1 0 : ℕ) = 1 ∧ x.2.2 {0} = some 0 then 1 else 0
            have hw0 : ∀ k x, 0 ≤ w k x := by
              intro k x
              refine mul_nonneg (mul_nonneg (hA.F_nonneg _ _) ?_) ((hlaw _ (hmem k) _).1 _)
              exact Finset.prod_nonneg fun i _ => hgnn _ _ _
            have hgd : ∑ d : Fin 1 → Fin (T+1), I.g 0 0 (d 0 : ℕ) = 1 := by
              rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (T+1)))
                (fun d => I.g 0 0 (d 0 : ℕ)) (fun e => I.g 0 0 (e : ℕ)) (fun d => rfl)]
              rw [Fin.sum_univ_eq_sum_range (fun e => I.g 0 0 e) (T+1)]
              rw [Finset.sum_range_eq_add_Ico _ (by omega), hg0, zero_add, ← hgsum 0 0]
              rfl
            have hwsum : ∀ k, ∑ x, w k x = 1 := by
              intro k
              rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
              simp only [w, hF, one_mul, Fin.prod_univ_one]
              rw [← Finset.sum_mul_sum, hgd, one_mul]
              exact (hlaw _ (hmem k) 0).2.1
            have hwh : ∀ k, 1/2 ≤ ∑ x, w k x * h x := by
              intro k
              rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
              let d1 : Fin 1 → Fin (T+1) := fun _ => ⟨1, by omega⟩
              have hs : ∑ f, w k (0, d1, f) * h (0, d1, f) ≤
                  ∑ d, ∑ f, w k (0, d, f) * h (0, d, f) := by
                refine Finset.single_le_sum (f := fun d => ∑ f, w k (0, d, f) * h (0, d, f))
                  (fun d _ => Finset.sum_nonneg fun f _ => mul_nonneg (hw0 _ _) ?_) (Finset.mem_univ d1)
                dsimp only [h]
                split_ifs <;> norm_num
              refine le_trans ?_ hs
              have hl := (hlaw _ (hmem k) 0).2.2 {0} (by rw [hfeas]; exact Finset.mem_univ _) 0
              rw [hphi, if_pos (Finset.mem_singleton_self _), Finset.sum_filter] at hl
              have he : ∑ f, w k (0, d1, f) * h (0, d1, f) = I.g 0 0 1 * 1 := by
                rw [← hl, Finset.mul_sum]
                refine Finset.sum_congr rfl fun f _ => ?_
                simp only [w, h, d1, hF, one_mul, Fin.prod_univ_one, true_and]
                split_ifs <;> ring
              rw [he, hg, if_pos rfl]
              split_ifs <;> norm_num
            -- the equivalence
            let e : (Fin T → X) ≃ OfflineReal 1 T (Fin 1) :=
              { toFun := fun p => (fun k => (p k).1, fun k => (p k).2.1, fun k => (p k).2.2)
                invFun := fun ω k => (ω.1 k, ω.2.1 k, ω.2.2 k)
                left_inv := fun p => rfl
                right_inv := fun ω => rfl }
            have hprob : ∀ p, offlineProb I law (e p) = ∏ k, w k (p k) := fun p => rfl
            have hmax : ∀ p, ∑ k, h (p k) ≤ offlineMax I (e p) := by
              intro p
              let A : Fin T → Finset (Fin 1) := fun k => if ((p k).2.1 0 : ℕ) = 1 then {0} else ∅
              have hAf : OfflineFeasible I (e p) A := by
                intro k
                refine ⟨by rw [hfeas]; exact Finset.mem_univ _, fun i _ => ?_⟩
                rw [hc]
                rw [Nat.lt_one_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                rintro j - ⟨hjk, ⟨-, hi⟩, hout⟩
                have hi0 : i = 0 := Subsingleton.elim _ _
                subst hi0
                have hd : ((p j).2.1 0 : ℕ) = 1 := by
                  by_contra hne
                  simp [A, hne] at hi
                have hout' : k.1 < j.1 + ((p j).2.1 0 : ℕ) := hout
                have hjk' : j.1 < k.1 := hjk
                omega
              have hrev : offlineRev I (e p) A = ∑ k, h (p k) := by
                unfold offlineRev
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Fin.sum_univ_one, hr]
                by_cases hd : ((p k).2.1 0 : ℕ) = 1
                · have hAk : A k = {0} := by simp only [A, if_pos hd]
                  have : offlineRented (e p) A k 0 ↔ (p k).2.2 {0} = some 0 := by
                    unfold offlineRented
                    rw [hAk]
                    simp [e]
                  simp only [h, this, hd, true_and]
                · have hAk : A k = ∅ := by simp only [A, if_neg hd]
                  have : ¬ offlineRented (e p) A k 0 := by
                    unfold offlineRented
                    rw [hAk]
                    simp
                  simp only [h, hd, false_and, if_false]
                  rw [if_neg this]
              rw [← hrev]
              unfold offlineMax
              exact le_ciSup (f := fun A : {A : Fin T → Finset (Fin 1) // OfflineFeasible I (e p) A} =>
                offlineRev I (e p) A.1) (Set.finite_range _).bddAbove ⟨A, hAf⟩
            have hkey : ∀ k, 1/2 ≤ ∑ p : Fin T → X, (∏ j, w j (p j)) * h (p k) := by
              intro k
              have h1 : ∑ p : Fin T → X, (∏ j, w j (p j)) * h (p k) =
                  ∑ p : Fin T → X, ∏ j, (w j (p j) * (if j = k then h (p j) else 1)) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.prod_mul_distrib (f := fun j => w j (p j)) (g := fun j => if j = k then h (p j) else 1),
                  Finset.prod_ite_eq' Finset.univ k (fun j => h (p j)),
                  if_pos (Finset.mem_univ k)]
              rw [h1]
              have h2 := Finset.prod_univ_sum (fun _ : Fin T => (Finset.univ : Finset X))
                (fun j x => w j x * (if j = k then h x else 1))
              rw [Fintype.piFinset_univ] at h2
              rw [← h2, Finset.prod_eq_single k]
              · simpa using hwh k
              · intro j _ hj
                simpa [hj] using hwsum j
              · intro hk; exact absurd (Finset.mem_univ _) hk
            unfold optOffline
            rw [← Equiv.sum_comp e]
            calc (T:ℝ)/2 = ∑ k : Fin T, (1/2 : ℝ) := by simp; ring
              _ ≤ ∑ k, ∑ p : Fin T → X, (∏ j, w j (p j)) * h (p k) :=
                  Finset.sum_le_sum fun k _ => hkey k
              _ = ∑ p : Fin T → X, (∏ j, w j (p j)) * ∑ k, h (p k) := by
                  rw [Finset.sum_comm]
                  simp only [Finset.mul_sum]
              _ ≤ _ := by
                  refine Finset.sum_le_sum fun p _ => ?_
                  rw [hprob]
                  exact mul_le_mul_of_nonneg_left (hmax p) (Finset.prod_nonneg fun j _ => hw0 _ _)
          refine ⟨1, 1, I, hA, hex, hLP2, fun law hlaw => ⟨hopt law hlaw, fun y hy => ?_⟩⟩
          have hTpos : (0:ℝ) < T := by exact_mod_cast hT
          calc lpObj I y ≤ 2 := hLP2 y hy
            _ = (4 / (T:ℝ)) * ((T:ℝ)/2) := by field_simp; norm_num
            _ ≤ _ := mul_le_mul_of_nonneg_left (hopt law hlaw) (by positivity)
