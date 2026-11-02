-- Prove2me | solution 1 for QuantumMaxCutEnergy.product_state_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T18:57:25.106479+00:00
-- url     : https://prove2.me/submissions/5e86e847-af71-4878-8622-5a192c79e01e

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace QuantumMaxCutEnergy

private lemma sum_pi_prod {n : ℕ} {R : Type*} [CommRing R] (f : Fin n → Bool → R) :
    ∑ x : Fin n → Bool, ∏ i, f i (x i) = ∏ i, ∑ b, f i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool)) f,
    Fintype.piFinset_univ]

private lemma sum_bool_eq {R : Type*} [AddCommMonoid R] (f : Bool → R) :
    ∑ b, f b = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide)]

private lemma star_prod {n : ℕ} (g : Fin n → ℂ) :
    star (∏ i, g i) = ∏ i, star (g i) := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has, star_mul, ih, mul_comm]

private lemma normSq_prod {n : ℕ} (g : Fin n → ℂ) :
    Complex.normSq (∏ i, g i) = ∏ i, Complex.normSq (g i) := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has, Complex.normSq_mul, ih]

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy

/-- **The energy of a product state.** For one-qubit amplitudes normalized at
every site, the product wave has edge energy `2 (1 - |⟨φ_i, φ_j⟩|²)`. -/
theorem product_state_energy (G : Input) (φ : Fin G.n → Bool → ℂ)
    (hunit : ∀ i, Complex.normSq (φ i true) + Complex.normSq (φ i false) = 1) :
    (∑ x : Fin G.n → Bool, Complex.normSq (∏ i, φ i (x i))) = 1 ∧
      ∀ e : Edge G.n, (∑ x : Fin G.n → Bool, Complex.normSq ((∏ i, φ i (x i)) -
          (∏ i, φ i (x ((Equiv.swap e.val.1 e.val.2) i))))) =
        2 * (1 - Complex.normSq (∑ a : Bool, star (φ e.val.1 a) * φ e.val.2 a)) := by
  have hnorm : ∀ i, ∑ b : Bool, Complex.normSq (φ i b) = 1 := by
    intro i
    rw [sum_bool_eq, add_comm]; exact hunit i
  have hA : ∑ x : Fin G.n → Bool, Complex.normSq (∏ i, φ i (x i)) = 1 := by
    calc ∑ x : Fin G.n → Bool, Complex.normSq (∏ i, φ i (x i))
        = ∑ x : Fin G.n → Bool, ∏ i, Complex.normSq (φ i (x i)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          exact normSq_prod (fun i => φ i (x i))
      _ = ∏ i, ∑ b : Bool, Complex.normSq (φ i b) :=
          sum_pi_prod (fun i b => Complex.normSq (φ i b))
      _ = 1 := by
          refine (Finset.prod_congr rfl (fun i _ => hnorm i)).trans ?_
          simp
  refine ⟨hA, fun e => ?_⟩
  set i := e.val.1
  set j := e.val.2
  have hij : i ≠ j := by have h := e.property; omega
  set σ : Equiv.Perm (Fin G.n) := Equiv.swap i j
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self i j k
  have hσi : σ i = j := Equiv.swap_apply_left i j
  have hσj : σ j = i := Equiv.swap_apply_right i j
  have hσk : ∀ k, k ≠ i → k ≠ j → σ k = k := fun k h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  -- the module-level inner product on one site
  have hconj : ∀ (z : ℂ), star z * z = (Complex.normSq z : ℂ) := by
    intro z
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  -- |B|² has the same total as |A|²
  have hB : ∑ x : Fin G.n → Bool, Complex.normSq (∏ k, φ k (x (σ k))) = 1 := by
    calc ∑ x : Fin G.n → Bool, Complex.normSq (∏ k, φ k (x (σ k)))
        = ∑ x : Fin G.n → Bool, ∏ k, Complex.normSq (φ (σ k) (x k)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [normSq_prod]
          exact Fintype.prod_equiv σ (fun k => Complex.normSq (φ k (x (σ k))))
            (fun k => Complex.normSq (φ (σ k) (x k))) (fun k => by rw [hσσ k])
      _ = ∏ k, ∑ b : Bool, Complex.normSq (φ (σ k) b) :=
          sum_pi_prod (fun k b => Complex.normSq (φ (σ k) b))
      _ = 1 := by
          refine (Finset.prod_congr rfl (fun k _ => hnorm (σ k))).trans ?_
          simp
  -- the cross sum
  have hC : ∑ x : Fin G.n → Bool, (star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k)))
      = (∑ a : Bool, star (φ i a) * φ j a) * (∑ a : Bool, star (φ j a) * φ i a) := by
    have h1 : ∀ x : Fin G.n → Bool,
        star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k))
          = ∏ k, (star (φ k (x k)) * φ (σ k) (x k)) := by
      intro x
      rw [star_prod]
      rw [show (∏ k, φ k (x (σ k))) = ∏ k, φ (σ k) (x k) from
        Fintype.prod_equiv σ _ _ (fun k => by rw [hσσ k])]
      rw [← Finset.prod_mul_distrib]
    calc ∑ x : Fin G.n → Bool, (star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k)))
        = ∑ x : Fin G.n → Bool, ∏ k, (star (φ k (x k)) * φ (σ k) (x k)) := by
          refine Finset.sum_congr rfl (fun x _ => h1 x)
      _ = ∏ k, ∑ b : Bool, (star (φ k b) * φ (σ k) b) :=
          sum_pi_prod (fun k b => star (φ k b) * φ (σ k) b)
      _ = (∑ a : Bool, star (φ i a) * φ j a) * (∑ a : Bool, star (φ j a) * φ i a) := by
          have hu : ∀ k, ∑ b : Bool, star (φ k b) * φ k b = 1 := by
            intro k
            rw [sum_bool_eq, hconj, hconj]
            rw [← Complex.ofReal_add, add_comm, hunit k, Complex.ofReal_one]
          have hrest : ∏ k ∈ (Finset.univ.erase i).erase j,
              (∑ b : Bool, star (φ k b) * φ (σ k) b) = 1 := by
            refine Finset.prod_eq_one (fun k hk => ?_)
            have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
            have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
            rw [hσk k hki hkj, hu k]
          have hprod : (∏ k : Fin G.n, ∑ b : Bool, (star (φ k b) * φ (σ k) b))
              = (∏ k ∈ (Finset.univ.erase i).erase j,
                    (∑ b : Bool, star (φ k b) * φ (σ k) b))
                  * (∑ b : Bool, star (φ j b) * φ (σ j) b)
                  * (∑ b : Bool, star (φ i b) * φ (σ i) b) := by
            have e1 : (∏ k : Fin G.n, ∑ b : Bool, (star (φ k b) * φ (σ k) b))
                = (∏ k ∈ (Finset.univ.erase i).erase j,
                    (∑ b : Bool, star (φ k b) * φ (σ k) b))
                  * (∑ b : Bool, star (φ j b) * φ (σ j) b)
                  * (∑ b : Bool, star (φ i b) * φ (σ i) b) := by
              rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin G.n)))
                  (h := Finset.mem_univ i),
                ← Finset.prod_erase_mul (s := ((Finset.univ : Finset (Fin G.n)).erase i))
                  (h := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
            exact e1
          rw [hprod, hrest, hσi, hσj]
          ring
  -- the pointwise normSq expansion and summation
  have hstar_re : ∀ z : ℂ, (star z).re = z.re := fun z => Complex.conj_re z
  have hnormSq_eq : ∀ z : ℂ, Complex.normSq z = (star z * z).re := by
    intro z; rw [hconj]; simp
  have hpoint : ∀ x : Fin G.n → Bool,
      Complex.normSq ((∏ k, φ k (x k)) - (∏ k, φ k (x (σ k))))
        = Complex.normSq (∏ k, φ k (x k)) + Complex.normSq (∏ k, φ k (x (σ k)))
          - 2 * (star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k))).re := by
    intro x
    rw [hnormSq_eq, hnormSq_eq, hnormSq_eq]
    have e : star ((∏ k, φ k (x k)) - (∏ k, φ k (x (σ k))))
          * ((∏ k, φ k (x k)) - (∏ k, φ k (x (σ k))))
        = star (∏ k, φ k (x k)) * (∏ k, φ k (x k))
          + star (∏ k, φ k (x (σ k))) * (∏ k, φ k (x (σ k)))
          - (star (∏ k, φ k (x k)) * (∏ k, φ k (x (σ k)))
            + star (∏ k, φ k (x (σ k))) * (∏ k, φ k (x k))) := by
      rw [star_sub]; ring
    rw [e]
    have ec : star (∏ k, φ k (x (σ k))) * (∏ k, φ k (x k))
        = star (star (∏ k, φ k (x k)) * (∏ k, φ k (x (σ k)))) := by
      rw [star_mul, star_star]
    rw [ec]
    simp only [Complex.sub_re, Complex.add_re, hstar_re]
    ring
  -- the cross-sum conjugate relation
  have hc : (∑ a : Bool, star (φ j a) * φ i a) = star (∑ a : Bool, star (φ i a) * φ j a) := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [star_mul, star_star]
  calc ∑ x : Fin G.n → Bool, Complex.normSq ((∏ k, φ k (x k)) - (∏ k, φ k (x (σ k))))
      = ∑ x : Fin G.n → Bool, (Complex.normSq (∏ k, φ k (x k))
          + Complex.normSq (∏ k, φ k (x (σ k)))
          - 2 * (star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k))).re) := by
        refine Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (∑ x : Fin G.n → Bool, Complex.normSq (∏ k, φ k (x k)))
          + (∑ x : Fin G.n → Bool, Complex.normSq (∏ k, φ k (x (σ k))))
          - 2 * (∑ x : Fin G.n → Bool, (star (∏ k, φ k (x k)) * ∏ k, φ k (x (σ k))).re) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 1 + 1 - 2 * ((∑ a : Bool, star (φ i a) * φ j a)
          * (∑ a : Bool, star (φ j a) * φ i a)).re := by
        rw [hA, hB, ← Complex.re_sum, hC]
    _ = 2 * (1 - Complex.normSq (∑ a : Bool, star (φ i a) * φ j a)) := by
        rw [hc]
        have hz : (∑ a : Bool, star (φ i a) * φ j a) * star (∑ a : Bool, star (φ i a) * φ j a)
            = ((Complex.normSq (∑ a : Bool, star (φ i a) * φ j a) : ℝ) : ℂ) := by
          rw [mul_comm, hconj]
        rw [hz, Complex.ofReal_re]
        ring

end QuantumMaxCutEnergy

/-- **The energy of a product state.** -/
theorem solution (G : QuantumMaxCutEnergy.Input) (φ : Fin G.n → Bool → ℂ)
    (hunit : ∀ i, Complex.normSq (φ i true) + Complex.normSq (φ i false) = 1) :
    (∑ x : Fin G.n → Bool, Complex.normSq (∏ i, φ i (x i))) = 1 ∧
      ∀ e : QuantumMaxCutEnergy.Edge G.n, (∑ x : Fin G.n → Bool,
          Complex.normSq ((∏ i, φ i (x i)) -
            (∏ i, φ i (x ((Equiv.swap e.val.1 e.val.2) i))))) =
        2 * (1 - Complex.normSq (∑ a : Bool, star (φ e.val.1 a) * φ e.val.2 a)) :=
  QuantumMaxCutEnergy.product_state_energy G φ hunit

#print axioms solution
