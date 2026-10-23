-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.characteristicTwo_power_sums
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:42:03.97762+00:00
-- url     : https://prove2.me/submissions/4a76a4a9-de02-4fa1-beb1-59f8f1301cf7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

namespace X8C2

open Polynomial Finset

variable {F : Type*} [Field F]

/-- shift operator on sequences -/
def T : Module.End F (ℕ → F) := LinearMap.funLeft F F (fun m : ℕ => m + 1)

lemma T_pow_apply (i : ℕ) (s : ℕ → F) (l : ℕ) : ((T (F := F)) ^ i) s l = s (l + i) := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    show ((T (F := F)) ^ i) s (l + 1) = _
    rw [ih]; congr 1; omega

lemma aeval_apply (f : F[X]) (s : ℕ → F) (l : ℕ) :
    (aeval (T (F := F)) f) s l = ∑ i ∈ range (f.natDegree + 1), f.coeff i * s (l + i) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, T_pow_apply, smul_eq_mul]

def Ann (f : F[X]) (s : ℕ → F) (M : ℕ) : Prop := ∀ l, M ≤ l → (aeval (T (F := F)) f) s l = 0

lemma Ann_mul {f : F[X]} {s : ℕ → F} {M : ℕ} (h : Ann f s M) (g : F[X]) : Ann (g * f) s M := by
  intro l hl
  rw [map_mul, Module.End.mul_apply, aeval_apply]
  refine sum_eq_zero fun i _ => ?_
  rw [h (l + i) (by omega), mul_zero]

lemma Ann_dvd {f g : F[X]} {s : ℕ → F} {M : ℕ} (h : Ann f s M) (hd : f ∣ g) : Ann g s M := by
  obtain ⟨q, rfl⟩ := hd; rw [mul_comm]; exact Ann_mul h q

lemma aeval_X_pow_mul (r : ℕ) (g : F[X]) (s : ℕ → F) (l : ℕ) :
    (aeval (T (F := F)) (X ^ r * g)) s l = (aeval (T (F := F)) g) s (l + r) := by
  rw [map_mul, Module.End.mul_apply, map_pow, aeval_X, T_pow_apply]

lemma aeval_expand (q : ℕ) (g : F[X]) (s : ℕ → F) (m : ℕ) :
    (aeval (T (F := F)) (expand F q g)) s (q * m) = (aeval (T (F := F)) g) (fun j => s (q * j)) m := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Pi.add_apply, Pi.add_apply, hf, hg]
  | monomial n a =>
    simp only [expand_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, smul_eq_mul, T_pow_apply]
    rw [mul_add, mul_comm n q]

/-- geometric sequences are annihilated by polynomials vanishing at the ratio -/
lemma aeval_geom (f : F[X]) (v : F) (hv : f.eval v = 0) (l : ℕ) :
    (aeval (T (F := F)) f) (fun m => v ^ m) l = 0 := by
  rw [aeval_apply]
  have : ∑ i ∈ range (f.natDegree + 1), f.coeff i * v ^ (l + i) = v ^ l * f.eval v := by
    rw [eval_eq_sum_range, mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [pow_add]; ring
  rw [this, hv, mul_zero]

section vdm
variable {d : ℕ} (v : Fin d → F) (M : ℕ)

def W : Matrix (Fin d) (Fin d) F := fun j i => v i ^ (M + (j : ℕ))

lemma W_det (hv : Function.Injective v) (h0 : ∀ i, v i ≠ 0) : (W v M).det ≠ 0 := by
  have : W v M = (Matrix.vandermonde v).transpose * Matrix.diagonal (fun i => v i ^ M) := by
    ext j i
    simp [W, Matrix.mul_diagonal, Matrix.vandermonde_apply, pow_add, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (h0 i))

lemma indep (hv : Function.Injective v) (h0 : ∀ i, v i ≠ 0) (β : Fin d → F)
    (h : ∀ m, M ≤ m → ∑ i, β i * v i ^ m = 0) : β = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (W_det v M hv h0)
  ext j
  simp only [Matrix.mulVec, dotProduct, W, Pi.zero_apply]
  rw [← h (M + j) (by omega)]
  exact sum_congr rfl fun i _ => mul_comm _ _

lemma solve (hv : Function.Injective v) (h0 : ∀ i, v i ≠ 0) (c : ℕ → F)
    (hc : Ann (∏ i, (X - C (v i))) c M) : ∃ γ : Fin d → F, ∀ m, M ≤ m → c m = ∑ i, γ i * v i ^ m := by
  have hu : IsUnit (W v M) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (W_det v M hv h0))
  obtain ⟨γ, hγ⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (fun j => c (M + j))
  refine ⟨γ, ?_⟩
  set σ : F[X] := ∏ i, (X - C (v i))
  have hσm : σ.Monic := monic_prod_X_sub_C _ _
  have hσd : σ.natDegree = d := by simp [σ]
  set e : ℕ → F := c - ∑ i, γ i • (fun m => v i ^ m) with he
  have he_apply : ∀ m, e m = c m - ∑ i, γ i * v i ^ m := by
    intro m; simp [he, Finset.sum_apply]
  have hAe : Ann σ e M := by
    intro l hl
    rw [he, map_sub, map_sum, Pi.sub_apply, hc l hl, Finset.sum_apply]
    rw [sum_eq_zero, sub_zero]
    intro i _
    rw [map_smul, Pi.smul_apply, aeval_geom, smul_zero]
    rw [eval_prod]; exact prod_eq_zero (mem_univ i) (by simp)
  have hinit : ∀ j, j < d → e (M + j) = 0 := by
    intro j hj
    rw [he_apply, sub_eq_zero]
    have := congrFun hγ ⟨j, hj⟩
    simp only [Matrix.mulVec, dotProduct, W] at this
    rw [← this]; exact sum_congr rfl fun i _ => mul_comm _ _
  have key : ∀ m, M ≤ m → e m = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hmd : m < M + d
      · have := hinit (m - M) (by omega); rwa [show M + (m - M) = m by omega] at this
      · obtain ⟨l, rfl⟩ : ∃ l, m = l + d := ⟨m - d, by omega⟩
        have h := hAe l (by omega)
        rw [aeval_apply, hσd, sum_range_succ] at h
        rw [sum_eq_zero (fun i hi => by rw [ih (l + i) (by simp at hi; omega) (by omega), mul_zero]),
          zero_add, ← hσd, hσm.coeff_natDegree, one_mul, hσd] at h
        exact h
  intro m hm
  have := key m hm
  rwa [he_apply, sub_eq_zero] at this

end vdm

end X8C2


namespace X8C2

open Polynomial Finset

variable {F : Type*} [Field F]

lemma D [IsAlgClosed F] [DecidableEq F] (Q : F[X]) (hQ : Q.Monic) (r : ℕ) (hr : Q.natDegree = r) (q : ℕ) (hq : r ≤ q) :
    Q ∣ X ^ r * (∏ b ∈ Q.roots.toFinset.filter (· ≠ 0), (X - C b)) ^ q := by
  set Z := Q.roots.toFinset.filter (· ≠ 0)
  have hcard : Multiset.card Q.roots = r := by
    rw [← hr, (IsAlgClosed.splits Q).natDegree_eq_card_roots]
  have hQe : Q = (Q.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ (by rw [hcard, hr])).symm
  have hR : X ^ r * (∏ b ∈ Z, (X - C b)) ^ q =
      ((Multiset.replicate r (0 : F) + q • Z.val).map fun a => X - C a).prod := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate,
      Multiset.map_nsmul, Multiset.prod_nsmul]
    simp only [sub_zero, C_0]; rfl
  rw [hR]; conv_lhs => rw [hQe]
  apply Multiset.prod_dvd_prod_of_le
  apply Multiset.map_le_map
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_replicate]
  have hca : Multiset.count a Q.roots ≤ r := hcard ▸ Multiset.count_le_card _ _
  by_cases ha : a = 0
  · subst ha; simp only [if_true]; omega
  · rw [if_neg (Ne.symm ha)]
    by_cases hm : a ∈ Q.roots
    · have : a ∈ Z := by simp [Z, hm, ha]
      rw [Multiset.count_eq_one_of_mem Z.nodup this]; omega
    · rw [Multiset.count_eq_zero_of_notMem hm]; omega

section char2
variable [CharP F 2]

lemma pinj (t : ℕ) : Function.Injective (fun x : F => x ^ (2 ^ t)) := by
  intro x y h
  have : (x - y) ^ (2 ^ t) = 0 := by rw [sub_pow_char_pow]; simp only at h; rw [h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp this)

lemma frob_iter (ω : ℕ → F) (hfrob : ∀ a : ℕ, ω (2*a) = ω a ^ 2) (t b : ℕ) :
    ω (2 ^ t * b) = ω b ^ (2 ^ t) := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, mul_comm (2^t) 2, mul_assoc, hfrob, ih, ← pow_mul, mul_comm]

theorem x8_main [IsAlgClosed F] (ω : ℕ → F) (N r : ℕ) (a : Fin r → F)
    (hrec : ∀ l, N ≤ l → ω (r+l) + ∑ j : Fin r, a j * ω (j.val + l) = 0)
    (hfrob : ∀ a : ℕ, ω (2*a) = ω a ^ 2) :
    ∃ (d : ℕ) (u : Fin d → F), Function.Injective u ∧ (∀ a : ℕ, 1 ≤ a → ω a = ∑ i : Fin d, u i ^ a) := by
  classical
  set Q : F[X] := X ^ r + ∑ j : Fin r, C (a j) * X ^ (j : ℕ) with hQdef
  have hdeg : (∑ j : Fin r, C (a j) * X ^ (j : ℕ)).degree < (r : WithBot ℕ) := degree_sum_fin_lt a
  have hQm : Q.Monic := monic_X_pow_add hdeg
  have hQd : Q.natDegree = r := by
    rw [hQdef, natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hAQ : Ann Q ω N := by
    intro l hl
    simp only [hQdef, map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, T_pow_apply]
    rw [← hrec l hl, add_comm l r]
    congr 1
    exact sum_congr rfl fun j _ => by rw [add_comm]
  set Z := Q.roots.toFinset.filter (· ≠ 0) with hZ
  set S : F[X] := ∏ b ∈ Z, (X - C b) with hSdef
  have hr2 : r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
  have hA1 : Ann (X ^ r * S ^ (2 ^ r)) ω N := Ann_dvd hAQ (D Q hQm r hQd (2 ^ r) hr2)
  have hSexp : S ^ (2 ^ r) = expand F (2 ^ r) (map (iterateFrobenius F 2 r) S) := by
    rw [← map_expand, map_iterateFrobenius_expand]
  set c : ℕ → F := fun j => ω (2 ^ r * j) with hc
  have hAc : Ann (map (iterateFrobenius F 2 r) S) c (N + r) := by
    intro m hm
    have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hmm : m ≤ 2 ^ r * m := Nat.le_mul_of_pos_left m hpos
    rw [hc, ← aeval_expand, ← hSexp]
    have h2 : 2 ^ r * m = (2 ^ r * m - r) + r := by omega
    rw [h2, ← aeval_X_pow_mul]
    exact hA1 _ (by omega)
  set e := Z.equivFin
  set u : Fin Z.card → F := fun i => (e.symm i : F) with hu
  have hu_inj : Function.Injective u := fun i j h => e.symm.injective (Subtype.ext h)
  have hu0 : ∀ i, u i ≠ 0 := fun i => (Finset.mem_filter.mp (e.symm i).2).2
  have hS : S = ∏ i, (X - C (u i)) := by
    rw [hSdef, ← Finset.prod_coe_sort Z]
    exact (Equiv.prod_comp e.symm (fun x : Z => X - C (x : F))).symm
  set v : Fin Z.card → F := fun i => u i ^ 2 ^ r with hv
  have hS' : map (iterateFrobenius F 2 r) S = ∏ i, (X - C (v i)) := by
    rw [hS, Polynomial.map_prod]; simp [iterateFrobenius_def, v]
  have hv_inj : Function.Injective v := (pinj r).comp hu_inj
  have hv0 : ∀ i, v i ≠ 0 := fun i => pow_ne_zero _ (hu0 i)
  obtain ⟨γ, hγ⟩ := solve v (N + r) hv_inj hv0 c (hS' ▸ hAc)
  have hidem : ∀ i, γ i - γ i ^ 2 = 0 := by
    have hw_inj : Function.Injective (fun i => v i ^ 2) := by
      intro i j h; exact hv_inj (pinj 1 (by simpa using h))
    have h := indep (fun i => v i ^ 2) (N + r) hw_inj (fun i => pow_ne_zero _ (hv0 i))
      (fun i => γ i - γ i ^ 2) (fun m hm => ?_)
    · intro i; exact congrFun h i
    · have h1 : c (2 * m) = c m ^ 2 := by
        simp only [hc]; rw [mul_left_comm, hfrob]
      rw [hγ (2 * m) (by omega), hγ m hm, sum_pow_char] at h1
      simp only [sub_mul, sum_sub_distrib]
      rw [sub_eq_zero]
      convert h1 using 1
      · exact sum_congr rfl fun i _ => by ring
      · exact sum_congr rfl fun i _ => by ring
  have hγ01 : ∀ i, γ i = 0 ∨ γ i = 1 := by
    intro i
    have h := hidem i
    have : γ i * (1 - γ i) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1).symm
  set I := univ.filter (fun i => γ i = 1)
  refine ⟨I.card, fun j => u (I.equivFin.symm j), hu_inj.comp (fun x y h => I.equivFin.symm.injective
    (Subtype.ext h)), ?_⟩
  intro b hb
  have hsum : ∑ j : Fin I.card, u (I.equivFin.symm j) ^ b = ∑ i ∈ I, u i ^ b := by
    rw [Equiv.sum_comp I.equivFin.symm (fun x : I => u x ^ b), Finset.sum_coe_sort I (fun i => u i ^ b)]
  rw [hsum]
  set J := N + r
  apply pinj (r + J)
  show ω b ^ 2 ^ (r + J) = (∑ i ∈ I, u i ^ b) ^ 2 ^ (r + J)
  have hJ : J ≤ 2 ^ J * b := le_trans (Nat.lt_two_pow_self).le (Nat.le_mul_of_pos_right _ hb)
  rw [← frob_iter ω hfrob, sum_pow_char_pow, pow_add, mul_assoc]
  show c (2 ^ J * b) = _
  rw [hγ _ hJ, Finset.sum_filter]
  refine sum_congr rfl fun i _ => ?_
  rcases hγ01 i with h | h
  · rw [h, zero_mul, if_neg zero_ne_one]
  · rw [h, one_mul, if_pos rfl, hv]
    simp only [← pow_mul]; congr 1; ring

end char2

end X8C2

open scoped BigOperators in
open QAlgorithms.Papers.Independent.Support21.P12 in
theorem solution (F : Type*) [Field F] [IsAlgClosed F] [CharP F 2]
    (omega : ℕ → F) (hrec : ∃ N : ℕ, RecurrenceFrom omega N)
    (hfrob : ∀ a : ℕ, omega (2*a) = omega a ^ 2) :
    ∃ (d : ℕ) (u : Fin d → F), Function.Injective u ∧
      (∀ a : ℕ, 1 ≤ a → omega a = ∑ i : Fin d, u i ^ a) ∧
      (omega 0 = 0 ∨ omega 0 = 1) := by
  obtain ⟨N, r, a, _, hrec⟩ := hrec
  obtain ⟨d, u, hu, hsum⟩ := X8C2.x8_main omega N r a hrec hfrob
  refine ⟨d, u, hu, hsum, ?_⟩
  have h := hfrob 0
  simp only [mul_zero] at h
  have : omega 0 * (omega 0 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)
