-- Prove2me | solution 1 for WeakGoldbach.prime_ladder_to_8875e30_strict
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T16:33:02.093278+00:00
-- url     : https://prove2.me/submissions/04a2dd94-ac60-4ec5-8034-ea60e29d9bab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders

set_option autoImplicit false

private theorem join_ladders
    (B ka kb : ℕ) (pa pb : ℕ → ℕ)
    (ha : ∀ i, i ≤ ka → Nat.Prime (pa i))
    (hb : ∀ i, i ≤ kb → Nat.Prime (pb i))
    (hsa : ∀ i, i < ka → pa i < pa (i+1) ∧ pa (i+1) < pa i + B)
    (hsb : ∀ i, i < kb → pb i < pb (i+1) ∧ pb (i+1) < pb i + B)
    (hjoin : pa ka < pb 0 ∧ pb 0 < pa ka + B) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      p 0 = pa 0 ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + B) ∧
      p k = pb kb := by
  let p : ℕ → ℕ := fun i => if i ≤ ka then pa i else pb (i - (ka+1))
  refine ⟨ka+kb+1, p, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : i ≤ ka
    · simpa only [p, if_pos h] using ha i h
    · have hj : i - (ka+1) ≤ kb := by omega
      simpa only [p, if_neg h] using hb (i-(ka+1)) hj
  · simp [p]
  · intro i hi
    by_cases h : i < ka
    · have h0 : i ≤ ka := by omega
      have h1 : i+1 ≤ ka := by omega
      simpa only [p, if_pos h0, if_pos h1] using hsa i h
    · by_cases he : i = ka
      · subst i
        simpa [p] using hjoin
      · have h0 : ¬ i ≤ ka := by omega
        have h1 : ¬ i+1 ≤ ka := by omega
        have hj : i-(ka+1) < kb := by omega
        have heq : i+1-(ka+1) = (i-(ka+1))+1 := by omega
        simpa only [p, if_neg h0, if_neg h1, heq] using hsb (i-(ka+1)) hj
  · have h : ¬ ka+kb+1 ≤ ka := by omega
    have heq : ka+kb+1-(ka+1) = kb := by omega
    simp only [p, if_neg h, heq]

private theorem prefix_ladder (b : ℕ) (hb : b < 492700) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      p 0 ≤ 4 * 10^18 ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4 * 10^18) ∧
      p k ≤ (b+1)*18014398509481984000000000 ∧
      (b+1)*18014398509481984000000000 < p k + 2*10^18 := by
  induction b with
  | zero =>
    obtain ⟨k,p,hp,hfirst,hsteps,hlast⟩ :=
      WeakGoldbach.helfgott_platt_block_ladders 0 hb
    refine ⟨k,p,hp,?_,hsteps,?_,?_⟩
    · have h := hfirst.2
      norm_num at h ⊢
      omega
    · simpa using hlast.1
    · simpa using hlast.2
  | succ b ih =>
    obtain ⟨ka,pa,hpa,ha0,hsa,hatop,haclose⟩ := ih (by omega)
    obtain ⟨kb,pb,hpb,hb0,hsb,hbtop⟩ :=
      WeakGoldbach.helfgott_platt_block_ladders (b+1) hb
    have hj : pa ka < pb 0 ∧ pb 0 < pa ka + 4*10^18 := by
      constructor
      · have h := hb0.1
        omega
      · have h := hb0.2
        norm_num at haclose h ⊢
        omega
    obtain ⟨k,p,hp,h0,hs,htop⟩ :=
      join_ladders (4*10^18) ka kb pa pb hpa hpb hsa hsb hj
    refine ⟨k,p,hp,?_,hs,?_,?_⟩
    · simpa only [h0] using ha0
    · simpa only [htop] using hbtop.1
    · simpa only [htop] using hbtop.2

theorem solution :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      p 0 ≤ 4 * 10 ^ 18 ∧
      (∀ i, i < k → p i < p (i + 1) ∧ p (i + 1) < p i + 4 * 10 ^ 18) ∧
      8875694145621773516800000000000 < p k + 4 * 10 ^ 18 := by
  obtain ⟨k,p,hp,h0,hs,_,htop⟩ := prefix_ladder 492699 (by decide)
  refine ⟨k,p,hp,h0,hs,?_⟩
  norm_num at htop ⊢
  omega
