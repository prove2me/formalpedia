-- Prove2me | solution 1 for RegevLWE.Correctness.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T14:07:09.356203+00:00
-- url     : https://prove2.me/submissions/42166b5f-536d-49e9-95c0-1c7e676e5174

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open scoped BigOperators
open RegevLWE.Correctness
namespace LWEWork
lemma iid_succ {p m : ℕ} [NeZero p] (χ : PMF (ZMod p)) :
    iidPMF χ (m+1) = χ.bind (fun x => (iidPMF χ m).map (Fin.cons x)) := by
  classical
  apply PMF.ext
  intro e
  have heq (x : ZMod p) (t : Fin m → ZMod p) :
      e = Fin.cons x t ↔ x = e 0 ∧ t = Fin.tail e := by
    constructor
    · intro h
      subst e
      simp
    · rintro ⟨rfl, rfl⟩
      simp
  simp only [iidPMF, PMF.ofFintype_apply, PMF.bind_apply, PMF.map_apply, heq]
  simp [Fin.prod_univ_succ, Fin.tail, ite_and]

lemma convPow_succ_left {p : ℕ} [NeZero p] (χ : PMF (ZMod p)) (k : ℕ) :
    convPow χ (k+1) = χ.bind (fun y => (convPow χ k).map (fun x => y+x)) := by
  simp only [convPow, PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  simp only [add_comm]

lemma sum_cons_subset {p m : ℕ} [NeZero p] (S : Finset (Fin (m+1)))
    (x : ZMod p) (t : Fin m → ZMod p) :
    (∑ i ∈ S, Fin.cons x t i) = (if 0 ∈ S then x else 0) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.succ ∈ S), t i := by
  classical
  calc
    _ = ∑ i : Fin (m+1), if i ∈ S then Fin.cons x t i else 0 := by simp
    _ = _ := by rw [Fin.sum_univ_succ]; simp [Finset.sum_filter]

lemma card_subset_succ {m : ℕ} (S : Finset (Fin (m+1))) :
    S.card = (if 0 ∈ S then 1 else 0) +
      (Finset.univ.filter (fun i : Fin m => i.succ ∈ S)).card := by
  classical
  calc
    _ = ∑ i : Fin (m+1), if i ∈ S then 1 else 0 := by simp
    _ = _ := by rw [Fin.sum_univ_succ]; simp
end LWEWork

theorem residue_law {p : ℕ} [NeZero p] {m : ℕ} (χ : PMF (ZMod p))
    (S : Finset (Fin m)) :
    (iidPMF χ m).map (fun e => ∑ i ∈ S, e i) = convPow χ S.card := by
  classical
  induction m with
  | zero =>
    have hS : S = ∅ := Subsingleton.elim _ _
    subst S
    simpa [convPow, Function.const_def] using
      (PMF.map_const (iidPMF χ 0) (0 : ZMod p))
  | succ m ih =>
    let T : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ S)
    have hs (x : ZMod p) :
        (fun e => ∑ i ∈ S, Fin.cons x e i) =
        (fun y => (if 0 ∈ S then x else 0) + y) ∘ (fun e => ∑ i ∈ T, e i) := by
      funext e
      exact LWEWork.sum_cons_subset S x e
    rw [LWEWork.iid_succ, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    change (χ.bind (fun x => (iidPMF χ m).map (fun e => ∑ i ∈ S, Fin.cons x e i))) = _
    simp_rw [hs, ← PMF.map_comp, ih T]
    have hc := LWEWork.card_subset_succ S
    change S.card = (if 0 ∈ S then 1 else 0) + T.card at hc
    by_cases h0 : (0 : Fin (m+1)) ∈ S
    · simp only [h0, ↓reduceIte] at hc ⊢
      rw [hc, Nat.add_comm, LWEWork.convPow_succ_left]
    · simp only [h0, ↓reduceIte, zero_add] at hc ⊢
      rw [PMF.bind_const, hc]
      exact PMF.map_id _


set_option autoImplicit false
open Matrix RegevLWE.Correctness

theorem residue_eq {p : ℕ} [NeZero p] {n m : ℕ} (a : Fin m → Fin n → ZMod p)
    (s : Fin n → ZMod p) (e : Fin m → ZMod p) (S : Finset (Fin m)) :
    (encrypt (publicKey a s e) 0 S).2 - (encrypt (publicKey a s e) 0 S).1 ⬝ᵥ s
        = ∑ i ∈ S, e i ∧
      (encrypt (publicKey a s e) 1 S).2 - (encrypt (publicKey a s e) 1 S).1 ⬝ᵥ s
        = ((p / 2 : ℕ) : ZMod p) + ∑ i ∈ S, e i := by
  have key : ∑ i ∈ S, (a i ⬝ᵥ s + e i) - (∑ i ∈ S, a i) ⬝ᵥ s = ∑ i ∈ S, e i := by
    rw [Finset.sum_add_distrib, sum_dotProduct]
    ring
  constructor
  · simp only [encrypt, publicKey]
    simpa using key
  · simp only [encrypt, publicKey]
    simp only [if_true]
    linear_combination key



open Matrix RegevLWE.Correctness

theorem rounding {p : ℕ} [NeZero p] (hp : 2 ≤ p) (x : ZMod p)
    (hx : (absZ x : ℝ) < ((p / 2 : ℕ) : ℝ) / 2) :
    absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) ∧
      decodeResidue x = 0 ∧
      decodeResidue (((p / 2 : ℕ) : ZMod p) + x) = 1 := by
  have hx' : 2 * absZ x < p / 2 := by
    have : (2 * absZ x : ℕ) < p / 2 := by
      exact_mod_cast (show (2 : ℝ) * (absZ x : ℝ) < ((p / 2 : ℕ) : ℝ) by linarith)
    exact this
  have hq : p / 2 < p := by omega
  have hval := x.val_lt
  have hc : (((p / 2 : ℕ) : ZMod p)).val = p / 2 := ZMod.val_natCast_of_lt hq
  have hsub : (x - ((p / 2 : ℕ) : ZMod p)).val =
      if p / 2 ≤ x.val then x.val - p / 2 else p - (p / 2 - x.val) := by
    split_ifs with h
    · simpa [hc] using (ZMod.val_sub (a := x) (b := ((p / 2 : ℕ) : ZMod p)) (by simpa [hc]))
    · have hd := ZMod.val_sub (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simp [hc]; omega)
      have he : (((p / 2 : ℕ) : ZMod p) - x) ≠ 0 := by
        intro he
        have := congrArg ZMod.val he
        simp [hd, hc] at this
        omega
      rw [← neg_sub, ZMod.neg_val, if_neg he, hd, hc]
  have hadd : ((((p / 2 : ℕ) : ZMod p) + x)).val =
      if p ≤ p / 2 + x.val then p / 2 + x.val - p else p / 2 + x.val := by
    split_ifs with h
    · simpa [hc] using (ZMod.val_add_of_le (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simpa [hc]))
    · simpa [hc] using (ZMod.val_add_of_lt (a := ((p / 2 : ℕ) : ZMod p)) (b := x) (by simp [hc]; omega))
  have h1 : absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) := by
    unfold absZ at *
    rw [hsub]
    split_ifs at * <;> omega
  have h2 : absZ x < absZ (((p / 2 : ℕ) : ZMod p) + x) := by
    unfold absZ at *
    rw [hadd]
    split_ifs at * <;> omega
  refine ⟨h1, by simp [decodeResidue, h1], ?_⟩
  have he : (((p / 2 : ℕ) : ZMod p) + x) - ((p / 2 : ℕ) : ZMod p) = x := by abel
  simp [decodeResidue, he, not_lt_of_ge h2.le]

#print axioms rounding

open RegevLWE.Correctness MeasureTheory Matrix
open scoped ENNReal
namespace CorrectWork
lemma bind_mass_lower {α β : Type*} (p : PMF α) (f : α → PMF β)
    (b : β) (r : ℝ≥0∞) (h : ∀ x, r ≤ f x b) : r ≤ (p.bind f) b := by
  rw [PMF.bind_apply]
  calc
    r = ∑' x, p x * r := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum (fun x => mul_le_mul' le_rfl (h x))

lemma good_decrypt {p n m : ℕ} [NeZero p] (hp : 2 ≤ p)
    (a : Fin m → Fin n → ZMod p) (s : Fin n → ZMod p)
    (e : Fin m → ZMod p) (S : Finset (Fin m)) (c : Fin 2)
    (h : (absZ (∑ i ∈ S, e i) : ℝ) < ((p / 2 : ℕ) : ℝ) / 2) :
    decrypt s (encrypt (publicKey a s e) c S) = c := by
  fin_cases c
  · change decodeResidue ((encrypt (publicKey a s e) 0 S).2 - (encrypt (publicKey a s e) 0 S).1 ⬝ᵥ s) = 0
    rw [(residue_eq a s e S).1]
    exact (rounding hp _ h).2.1
  · change decodeResidue ((encrypt (publicKey a s e) 1 S).2 - (encrypt (publicKey a s e) 1 S).1 ⬝ᵥ s) = 1
    rw [(residue_eq a s e S).2]
    exact (rounding hp _ h).2.2

lemma fixed_subset {p n m : ℕ} [NeZero p] (hp : 2 ≤ p)
    (χ : PMF (ZMod p)) (δ : ℝ)
    (hχ : ∀ k ≤ m, 1 - δ <
      ((convPow χ k).toOuterMeasure {e | (absZ e : ℝ) < ((p / 2 : ℕ) : ℝ) / 2}).toReal)
    (a : Fin m → Fin n → ZMod p) (s : Fin n → ZMod p)
    (S : Finset (Fin m)) (c : Fin 2) :
    ENNReal.ofReal (1-δ) ≤
      ((iidPMF χ m).map (fun e => decrypt s (encrypt (publicKey a s e) c S))) c := by
  have hcard : S.card ≤ m := by simpa using Finset.card_le_univ S
  have hmass := ENNReal.ofReal_le_of_le_toReal (hχ S.card hcard).le
  rw [← residue_law χ S, PMF.toOuterMeasure_map_apply] at hmass
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  refine hmass.trans (measure_mono ?_)
  intro e he
  exact good_decrypt hp a s e S c he
end CorrectWork

open RegevLWE.Correctness
open scoped ENNReal

theorem solution {p : ℕ} [NeZero p] (hp : 2 ≤ p) (n m : ℕ)
    (χ : PMF (ZMod p)) (δ : ℝ) (hδ : 0 < δ)
    (hχ : ∀ k ≤ m, 1 - δ <
      ((convPow χ k).toOuterMeasure {e | (absZ e : ℝ) < ((p / 2 : ℕ) : ℝ) / 2}).toReal)
    (c : Fin 2) : 1 - δ ≤ (outcome n m χ c c).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal ((outcome n m χ c).apply_ne_top c)).mp
  unfold outcome
  apply CorrectWork.bind_mass_lower
  intro s
  apply CorrectWork.bind_mass_lower
  intro a
  change ENNReal.ofReal (1 - δ) ≤
    ((iidPMF χ m).bind (fun e =>
      (PMF.uniformOfFintype (Finset (Fin m))).bind (fun S =>
        PMF.pure (decrypt s (encrypt (publicKey a s e) c S))))) c
  rw [PMF.bind_comm]
  apply CorrectWork.bind_mass_lower
  intro S
  exact CorrectWork.fixed_subset hp χ δ hχ a s S c
#print axioms solution
