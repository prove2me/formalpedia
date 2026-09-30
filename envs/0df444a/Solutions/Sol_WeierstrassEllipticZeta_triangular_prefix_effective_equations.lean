-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_prefix_effective_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T20:16:57.796025+00:00
-- url     : https://prove2.me/submissions/db1c1306-c40f-4984-a80d-b118ae2ac679

import Theorems.Thm_WeierstrassEllipticZeta_triangular_prefix_gcd_recurrence
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

noncomputable section
open scoped Classical

open WeierstrassEllipticZeta

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) :
    let J := fun s : ℕ => I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
    ∀ n : ℕ,
      let T := (Finset.range n).filter (fun i => p i ∉ J i)
      J n = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
      T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J n) ≤ M.natDegree := by
  classical
  let G : ℕ → Polynomial ℂ := Nat.rec M (fun s g =>
    gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s)))
  let J := fun s : ℕ => I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
  let T := fun n : ℕ => (Finset.range n).filter (fun i => p i ∉ J i)
  have hrec := triangular_prefix_gcd_recurrence I M r hM hI p
  have hJsucc (s : ℕ) : J (s + 1) = J s ⊔ Ideal.span {p s} := by
    have hfun : (fun i : Fin (s + 1) => p i.val) =
        Fin.snoc (fun i : Fin s => p i.val) (p s) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    dsimp only [J]
    rw [hfun, Fin.range_snoc, Ideal.span_insert]
    ac_rfl
  have hTsucc (s : ℕ) : T (s + 1) =
      if p s ∉ J s then insert s (T s) else T s := by
    dsimp only [T]
    rw [Finset.range_add_one, Finset.filter_insert]
  have hkeep (n : ℕ) : J n = I ⊔ Ideal.span (p '' (T n : Set ℕ)) ∧
      (T n).card + (G n).natDegree ≤ M.natDegree := by
    induction n with
    | zero => simp [J, T, G]
    | succ n ih =>
      obtain ⟨_, _, _, _, _, _, hle, _, hstrict, _⟩ := hrec.2.2 n
      have hle' : (G (n + 1)).natDegree ≤ (G n).natDegree := hle
      by_cases hp : p n ∈ J n
      · have ht : T (n + 1) = T n := by
          rw [hTsucc, if_neg (not_not_intro hp)]
        have hj : J (n + 1) = J n := by
          rw [hJsucc]
          exact sup_of_le_left ((Ideal.span_singleton_le_iff_mem _).mpr hp)
        constructor
        · rw [hj, ht]
          exact ih.1
        · rw [ht]
          omega
      · have ht : T (n + 1) = insert n (T n) := by
          rw [hTsucc, if_pos hp]
        have hn : n ∉ T n := by simp [T]
        have hdrop : (G (n + 1)).natDegree < (G n).natDegree := hstrict.mpr hp
        constructor
        · rw [hJsucc, ih.1, ht, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
          ac_rfl
        · rw [ht, Finset.card_insert_of_notMem hn]
          omega
  change ∀ n : ℕ, J n = I ⊔ Ideal.span (p '' (T n : Set ℕ)) ∧
    (T n).card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J n) ≤ M.natDegree
  intro n
  obtain ⟨hgen, hbound⟩ := hkeep n
  refine ⟨hgen, ?_⟩
  obtain ⟨_, _, _, _, hlength, _⟩ := hrec.2.2 n
  change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J n) = (G n).natDegree at hlength
  rw [hlength]
  exact hbound

