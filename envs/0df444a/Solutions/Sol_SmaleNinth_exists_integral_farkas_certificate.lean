-- Prove2me | solution 1 for SmaleNinth.exists_integral_farkas_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T06:44:21.569312+00:00
-- url     : https://prove2.me/submissions/469a65d6-518b-4f21-aa2a-949242ffa2dc

import Mathlib
import Definitions.Def_Polyhedron
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Theorems.Thm_SmaleNinth_exists_square_subsystem
import Theorems.Thm_SmaleNinth_abs_det_le_factorial_mul_pow

open Matrix LinearOptimization

namespace FarkasCert

variable {m n : ℕ}







/-- An infeasible system `Ax ≥ b` has a nonnegative real Farkas certificate
with `y'A = 0` and `y'b ≥ 1`. -/
theorem farkas_of_empty (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hempty : polyhedron A b = ∅) :
    ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧
      1 ≤ ∑ i, y i * b i := by
  classical
  set Ab : Matrix (Fin m ⊕ Unit) (Fin (n + 1)) ℝ :=
    Sum.elim (fun i => Fin.cons (b i) (fun j => -(A i j)))
             (fun _ => Fin.cons (-1) 0) with hAb
  have e_inl_zero : ∀ i, Ab (Sum.inl i) 0 = b i := by intro i; simp [hAb]
  have e_inl_succ : ∀ (i : Fin m) (j : Fin n), Ab (Sum.inl i) j.succ = -(A i j) := by
    intro i j; simp [hAb]
  have e_inr_zero : Ab (Sum.inr ()) 0 = -1 := by simp [hAb]
  have e_inr_succ : ∀ j : Fin n, Ab (Sum.inr ()) j.succ = 0 := by intro j; simp [hAb]
  have hmulVec : ∀ (x : Fin (n + 1) → ℝ) (r : Fin m ⊕ Unit),
      Ab.mulVec x r = ∑ j : Fin (n + 1), Ab r j * x j := by
    intro x r; rfl
  have hT : ∀ (p : (Fin m ⊕ Unit) → ℝ) (j : Fin (n + 1)),
      Abᵀ.mulVec p j
        = (∑ i, Ab (Sum.inl i) j * p (Sum.inl i)) + Ab (Sum.inr ()) j * p (Sum.inr ()) := by
    intro p j
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hfeas : ∃ x : Fin (n + 1) → ℝ, Ab.mulVec x ≤ 0 := by
    refine ⟨0, ?_⟩; simp [Matrix.mulVec_zero]
  have hkey : ∀ x : Fin (n + 1) → ℝ, Ab.mulVec x ≤ 0 →
      (Fin.cons (1 : ℝ) 0 : Fin (n + 1) → ℝ) ⬝ᵥ x ≤ 0 := by
    intro x hx
    have hc : (Fin.cons (1 : ℝ) 0 : Fin (n + 1) → ℝ) ⬝ᵥ x = x 0 := by
      simp [dotProduct, Fin.sum_univ_succ]
    rw [hc]
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < x 0 := hcon
    have hrow : ∀ i : Fin m, b i * x 0 ≤ ∑ j : Fin n, A i j * x j.succ := by
      intro i
      have h1 : Ab.mulVec x (Sum.inl i) ≤ 0 := hx (Sum.inl i)
      rw [hmulVec, Fin.sum_univ_succ, e_inl_zero i] at h1
      have h2 : ∑ j : Fin n, Ab (Sum.inl i) j.succ * x j.succ
          = -∑ j : Fin n, A i j * x j.succ := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun j _ => by rw [e_inl_succ i j]; ring)
      rw [h2] at h1
      linarith
    have hmem : ((x 0)⁻¹ • (fun j : Fin n => x j.succ)) ∈ polyhedron A b := by
      rw [polyhedron, Set.mem_setOf_eq, Pi.le_def]
      intro i
      have hval : A.mulVec ((x 0)⁻¹ • (fun j : Fin n => x j.succ)) i
          = (∑ j : Fin n, A i j * x j.succ) / x 0 := by
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
          div_eq_inv_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hval, le_div_iff₀ hpos]
      exact hrow i
    rw [hempty] at hmem
    exact hmem
  obtain ⟨p, hp0, hpc, -⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype Ab 0
      (Fin.cons (1 : ℝ) 0) 0 hfeas).mp hkey
  refine ⟨fun i => p (Sum.inl i), fun i => hp0 (Sum.inl i), ?_, ?_⟩
  · intro j
    have h := congrFun hpc j.succ
    rw [hT p j.succ] at h
    have hz : (Fin.cons (1 : ℝ) 0 : Fin (n + 1) → ℝ) j.succ = 0 := by simp
    rw [hz, e_inr_succ j, zero_mul, add_zero] at h
    have h2 : ∑ i, Ab (Sum.inl i) j.succ * p (Sum.inl i)
        = -∑ i, p (Sum.inl i) * A i j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [e_inl_succ i j]; ring)
    rw [h2, neg_eq_zero] at h
    exact h
  · have h := congrFun hpc 0
    rw [hT p 0] at h
    have hz : (Fin.cons (1 : ℝ) 0 : Fin (n + 1) → ℝ) 0 = 1 := by simp
    rw [hz, e_inr_zero] at h
    have h2 : ∑ i, Ab (Sum.inl i) 0 * p (Sum.inl i)
        = ∑ i, p (Sum.inl i) * b i :=
      Finset.sum_congr rfl (fun i _ => by rw [e_inl_zero i]; ring)
    rw [h2] at h
    have hnn : 0 ≤ p (Sum.inr ()) := hp0 (Sum.inr ())
    linarith






/-- A normalized nonnegative Farkas certificate. -/
def Cert (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ (∑ i, y i * b i) = 1

/-- A linear relation among the rows of `[A | b]`. -/
def Rel (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (mu : Fin m → ℝ) : Prop :=
  (∀ j, ∑ i, mu i * A i j = 0) ∧ (∑ i, mu i * b i) = 0

/-- Support of a vector, as a `Finset`. -/
noncomputable def supp (y : Fin m → ℝ) : Finset (Fin m) := Finset.univ.filter (fun i => y i ≠ 0)

lemma mem_supp {y : Fin m → ℝ} {i : Fin m} : i ∈ supp y ↔ y i ≠ 0 := by
  simp [supp]

/-- Sliding a certificate along a relation with a negative coordinate kills a
coordinate of the support. -/
lemma shrink (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y mu : Fin m → ℝ)
    (hy : Cert A b y) (hrel : Rel A b mu) (hsupp : ∀ i, y i = 0 → mu i = 0)
    (i0 : Fin m) (hi0 : mu i0 < 0) :
    ∃ z, Cert A b z ∧ (supp z).card < (supp y).card := by
  classical
  set T : Finset (Fin m) := Finset.univ.filter (fun i => mu i < 0) with hTdef
  have hTne : T.Nonempty := ⟨i0, by simp [hTdef, hi0]⟩
  obtain ⟨i1, hi1mem, hi1min⟩ :=
    T.exists_min_image (fun i => y i / (-(mu i))) hTne
  have hmu1 : mu i1 < 0 := by simpa [hTdef] using hi1mem
  have hy1 : 0 < y i1 := by
    rcases lt_or_eq_of_le (hy.1 i1) with h | h
    · exact h
    · exact absurd (hsupp i1 h.symm) (ne_of_lt hmu1)
  have hneg1 : 0 < -(mu i1) := by linarith
  have hmun : mu i1 ≠ 0 := ne_of_lt hmu1
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = y i1 / (-(mu i1)) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; exact div_pos hy1 hneg1
  have h1 : t * (-(mu i1)) = y i1 := by rw [htdef]; field_simp
  have hmin' : ∀ i, mu i < 0 → t ≤ y i / (-(mu i)) := by
    intro i hi
    rw [htdef]
    exact hi1min i (by simp [hTdef, hi])
  refine ⟨fun i => y i + t * mu i, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    by_cases h : 0 ≤ mu i
    · have : 0 ≤ t * mu i := mul_nonneg (le_of_lt ht) h
      have := hy.1 i
      linarith
    · push_neg at h
      have hiT : i ∈ T := by simp [hTdef, h]
      have hle : t ≤ y i / (-(mu i)) := hmin' i h
      have hpos : 0 < -(mu i) := by linarith
      rw [le_div_iff₀ hpos] at hle
      linarith
  · intro j
    have : ∀ i, (y i + t * mu i) * A i j = y i * A i j + t * (mu i * A i j) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hy.2.1 j, hrel.1 j, mul_zero, add_zero]
  · have : ∀ i, (y i + t * mu i) * b i = y i * b i + t * (mu i * b i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hy.2.2, hrel.2, mul_zero, add_zero]
  · have hsub : supp (fun i => y i + t * mu i) ⊆ supp y := by
      intro i hi
      rw [mem_supp] at hi ⊢
      intro hzero
      rw [hzero, hsupp i hzero, mul_zero, add_zero] at hi
      exact hi rfl
    have hi1y : i1 ∈ supp y := by rw [mem_supp]; exact ne_of_gt hy1
    have hi1z : i1 ∉ supp (fun i => y i + t * mu i) := by
      rw [mem_supp]
      push_neg
      linear_combination -h1
    exact Finset.card_lt_card (HasSubset.Subset.ssubset_of_ne hsub
      (fun h => hi1z (h ▸ hi1y)))

/-- Every certificate can be replaced by one whose support carries no
nontrivial relation. -/
theorem exists_minimal_cert (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (y0 : Fin m → ℝ) (h0 : Cert A b y0) :
    ∃ z, Cert A b z ∧
      ∀ mu, Rel A b mu → (∀ i, z i = 0 → mu i = 0) → mu = 0 := by
  classical
  suffices H : ∀ k (y : Fin m → ℝ), Cert A b y → (supp y).card ≤ k →
      ∃ z, Cert A b z ∧ ∀ mu, Rel A b mu → (∀ i, z i = 0 → mu i = 0) → mu = 0 by
    exact H _ y0 h0 le_rfl
  intro k
  induction k with
  | zero =>
      intro y hy hcard
      exfalso
      have hz : ∀ i, y i = 0 := by
        intro i
        by_contra hne
        have hmem : i ∈ supp y := by rw [mem_supp]; exact hne
        have := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      have h1 := hy.2.2
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
        rw [hz i]; ring : ∀ i ∈ Finset.univ, y i * b i = 0)] at h1
      simp at h1
  | succ k ih =>
      intro y hy hcard
      by_cases hindep : ∀ mu, Rel A b mu → (∀ i, y i = 0 → mu i = 0) → mu = 0
      · exact ⟨y, hy, hindep⟩
      · push_neg at hindep
        obtain ⟨mu, hrel, hsupp, hmune⟩ := hindep
        obtain ⟨i0, hi0⟩ : ∃ i, mu i ≠ 0 := Function.ne_iff.mp hmune
        have hshrink : ∃ z, Cert A b z ∧ (supp z).card < (supp y).card := by
          rcases lt_or_gt_of_ne hi0 with hneg | hpos
          · exact shrink A b y mu hy hrel hsupp i0 hneg
          · refine shrink A b y (fun i => -(mu i)) hy ⟨?_, ?_⟩ ?_ i0 (by simpa using hpos)
            · intro j
              have : ∀ i, -(mu i) * A i j = -(mu i * A i j) := fun i => by ring
              rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_neg_distrib,
                hrel.1 j, neg_zero]
            · have : ∀ i, -(mu i) * b i = -(mu i * b i) := fun i => by ring
              rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_neg_distrib,
                hrel.2, neg_zero]
            · intro i hi; rw [hsupp i hi, neg_zero]
        obtain ⟨z, hzc, hzlt⟩ := hshrink
        exact ih z hzc (by omega)






/-- Reindexing a sum supported on a finset along its order isomorphism. -/
lemma sum_reindex {s : ℕ} (S : Finset (Fin m)) (hs : S.card = s) (f : Fin m → ℝ)
    (h0 : ∀ i ∉ S, f i = 0) :
    ∑ i, f i = ∑ k : Fin s, f ((S.orderIsoOfFin hs k : Fin m)) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => h0 i hi)]
  rw [← Finset.sum_coe_sort S f]
  exact (Fintype.sum_equiv (S.orderIsoOfFin hs).toEquiv
    (fun k => f ((S.orderIsoOfFin hs k : Fin m))) (fun x : S => f (x : Fin m))
    (fun k => rfl)).symm

/-- The `(n+1) × s` integer matrix whose `k`-th column is the row
`(b (sg k), A (sg k) ·)` of `[b | A]`. -/
def colMat (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) {s : ℕ}
    (sg : Fin s → Fin m) : Matrix (Fin (n + 1)) (Fin s) ℤ :=
  fun r k => (Fin.cons (b (sg k)) (fun j => A (sg k) j) : Fin (n + 1) → ℤ) r

/-- The target vector `(1, 0, …, 0)`. -/
def tgt (n : ℕ) : Fin (n + 1) → ℤ := Fin.cons 1 0

@[simp] lemma colMat_zero (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) {s : ℕ}
    (sg : Fin s → Fin m) (k : Fin s) : colMat A b sg 0 k = b (sg k) := by
  simp [colMat]

@[simp] lemma colMat_succ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) {s : ℕ}
    (sg : Fin s → Fin m) (k : Fin s) (j : Fin n) :
    colMat A b sg j.succ k = A (sg k) j := by
  simp [colMat]

@[simp] lemma tgt_zero (n : ℕ) : tgt n 0 = 1 := by simp [tgt]

@[simp] lemma tgt_succ (n : ℕ) (j : Fin n) : tgt n j.succ = 0 := by simp [tgt]

lemma colMat_entry_bound (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) {s : ℕ}
    (sg : Fin s → Fin m) (U : ℕ) (hA : ∀ i j, |A i j| ≤ (U : ℤ))
    (hb : ∀ i, |b i| ≤ (U : ℤ)) : ∀ r k, |colMat A b sg r k| ≤ (U : ℤ) := by
  intro r k
  induction r using Fin.cases with
  | zero => rw [colMat_zero]; exact hb _
  | succ j => rw [colMat_succ]; exact hA _ _

lemma tgt_entry_bound (n : ℕ) (U : ℕ) (hU : 1 ≤ U) : ∀ r, |tgt n r| ≤ (U : ℤ) := by
  intro r
  induction r using Fin.cases with
  | zero => rw [tgt_zero]; simpa using hU
  | succ j => rw [tgt_succ]; positivity







lemma map_updateCol {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (k : Fin r) (v : Fin r → ℤ) :
    (M.map (Int.cast : ℤ → ℝ)).updateCol k (fun i => ((v i : ℤ) : ℝ))
      = (M.updateCol k v).map (Int.cast : ℤ → ℝ) := by
  classical
  ext i j
  by_cases h : j = k <;> simp [Matrix.updateCol_apply, h]

lemma det_map_cast {r : ℕ} (P : Matrix (Fin r) (Fin r) ℤ) :
    (P.map (Int.cast : ℤ → ℝ)).det = ((P.det : ℤ) : ℝ) := by
  have h := RingHom.map_det (Int.castRingHom ℝ) P
  simpa [RingHom.mapMatrix_apply] using h.symm

lemma sum_swap_ite {m r : ℕ} (f : Fin r → Fin m) (c : Fin r → ℤ) (w : Fin m → ℤ) :
    ∑ i, (∑ k : Fin r, if f k = i then c k else 0) * w i
      = ∑ k : Fin r, c k * w (f k) := by
  classical
  have h1 : ∀ i : Fin m, (∑ k : Fin r, if f k = i then c k else 0) * w i
      = ∑ k : Fin r, (if f k = i then c k * w i else 0) := by
    intro i
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by by_cases h : f k = i <;> simp [h])
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => by simp)

lemma sum_swap_ite' {m r : ℕ} (f : Fin r → Fin m) (c : Fin r → ℤ) :
    ∑ i, (∑ k : Fin r, if f k = i then c k else 0) = ∑ k : Fin r, c k := by
  have := sum_swap_ite f c (fun _ => 1)
  simpa using this

/-- **An infeasible integer system has an integral Farkas certificate of bounded
`ℓ¹` norm.** -/
theorem main (U : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hempty : polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) = ∅) :
    ∃ y : Fin m → ℤ, (∀ i, 0 ≤ y i) ∧
      (∀ j, ∑ i, y i * A i j = 0) ∧
      1 ≤ ∑ i, y i * b i ∧
      (∑ i, y i) ≤ ((n + 1) * (n + 1).factorial * U ^ (n + 1) : ℤ) := by
  classical
  set Ar : Matrix (Fin m) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ) with hAr
  set br : Fin m → ℝ := fun i => (b i : ℝ) with hbr
  have hArval : ∀ i j, Ar i j = ((A i j : ℤ) : ℝ) := fun i j => rfl
  -- 1. a real Farkas certificate, normalized
  obtain ⟨y0, hy0nn, hy0A, hy0b⟩ := farkas_of_empty Ar br hempty
  have hCpos : 0 < ∑ i, y0 i * br i := lt_of_lt_of_le zero_lt_one hy0b
  have hcert : Cert Ar br (fun i => y0 i / (∑ i, y0 i * br i)) := by
    refine ⟨fun i => div_nonneg (hy0nn i) (le_of_lt hCpos), ?_, ?_⟩
    · intro j
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        (by ring : y0 i / (∑ i, y0 i * br i) * Ar i j
              = y0 i * Ar i j / (∑ i, y0 i * br i))),
        ← Finset.sum_div, hy0A j, zero_div]
    · rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        (by ring : y0 i / (∑ i, y0 i * br i) * br i
              = y0 i * br i / (∑ i, y0 i * br i))),
        ← Finset.sum_div, div_self (ne_of_gt hCpos)]
  -- 2. a certificate whose support carries no relation
  obtain ⟨z, hz, hmin⟩ := exists_minimal_cert Ar br _ hcert
  set S : Finset (Fin m) := supp z with hS
  have hzout : ∀ i ∉ S, z i = 0 := by
    intro i hi
    by_contra h
    exact hi (mem_supp.mpr h)
  -- 3. enumerate the support
  obtain ⟨sg, ext, hsg_mem, hreidx, hext_sg, hext_out⟩ :
      ∃ (sg : Fin S.card → Fin m) (ext : (Fin S.card → ℝ) → (Fin m → ℝ)),
        (∀ k, sg k ∈ S) ∧
        (∀ f : Fin m → ℝ, (∀ i ∉ S, f i = 0) → ∑ i, f i = ∑ k, f (sg k)) ∧
        (∀ (mu : Fin S.card → ℝ) k, ext mu (sg k) = mu k) ∧
        (∀ (mu : Fin S.card → ℝ) i, i ∉ S → ext mu i = 0) := by
    refine ⟨fun k => ((S.orderIsoOfFin rfl k : Fin m)),
      fun mu i => if h : i ∈ S then mu ((S.orderIsoOfFin rfl).symm ⟨i, h⟩) else 0,
      fun k => (S.orderIsoOfFin rfl k).2,
      fun f h0 => sum_reindex S rfl f h0, ?_, fun mu i hi => dif_neg hi⟩
    intro mu k
    have hmem : ((S.orderIsoOfFin rfl k : Fin m)) ∈ S := (S.orderIsoOfFin rfl k).2
    dsimp only
    rw [dif_pos hmem]
    congr 1
    have he : (⟨((S.orderIsoOfFin rfl k : Fin m)), hmem⟩ : {x // x ∈ S})
        = S.orderIsoOfFin rfl k := Subtype.ext rfl
    rw [he]
    exact (S.orderIsoOfFin rfl).symm_apply_apply k
  have hznz : ∀ k, z (sg k) ≠ 0 := fun k => mem_supp.mp (hsg_mem k)
  -- 4. the reduced (n+1) × |S| system
  set M : Matrix (Fin (n + 1)) (Fin S.card) ℤ := colMat A b sg with hM
  set Mr : Matrix (Fin (n + 1)) (Fin S.card) ℝ := M.map (Int.cast : ℤ → ℝ) with hMr
  set zz : Fin S.card → ℝ := fun k => z (sg k) with hzz
  have hMr_zero : ∀ k, Mr 0 k = br (sg k) := by intro k; simp [hMr, hM, hbr]
  have hMr_succ : ∀ (j : Fin n) (k), Mr j.succ k = Ar (sg k) j := by
    intro j k; simp [hMr, hM, hAr]
  have hMeq : Mr.mulVec zz = fun r => ((tgt n r : ℤ) : ℝ) := by
    funext rr
    induction rr using Fin.cases with
    | zero =>
        have h1 : Mr.mulVec zz 0 = ∑ k, z (sg k) * br (sg k) := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun k _ => by rw [hMr_zero k]; ring)
        rw [h1, ← hreidx (fun i => z i * br i) (fun i hi => by rw [hzout i hi]; ring), hz.2.2]
        simp
    | succ j =>
        have h1 : Mr.mulVec zz j.succ = ∑ k, z (sg k) * Ar (sg k) j := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun k _ => by rw [hMr_succ j k]; ring)
        rw [h1, ← hreidx (fun i => z i * Ar i j) (fun i hi => by rw [hzout i hi]; ring),
          hz.2.1 j]
        simp
  -- 5. the columns are independent
  have hinj : ∀ mu : Fin S.card → ℝ, Mr.mulVec mu = 0 → mu = 0 := by
    intro mu hmu
    have hrel : Rel Ar br (ext mu) := by
      constructor
      · intro j
        rw [hreidx (fun i => ext mu i * Ar i j)
          (fun i hi => by rw [hext_out mu i hi]; ring)]
        have hh : ∀ k, ext mu (sg k) * Ar (sg k) j = Mr j.succ k * mu k := by
          intro k; rw [hext_sg mu k, hMr_succ j k]; ring
        rw [Finset.sum_congr rfl (fun k _ => hh k)]
        have := congrFun hmu j.succ
        simpa [Matrix.mulVec, dotProduct] using this
      · rw [hreidx (fun i => ext mu i * br i)
          (fun i hi => by rw [hext_out mu i hi]; ring)]
        have hh : ∀ k, ext mu (sg k) * br (sg k) = Mr 0 k * mu k := by
          intro k; rw [hext_sg mu k, hMr_zero k]; ring
        rw [Finset.sum_congr rfl (fun k _ => hh k)]
        have := congrFun hmu 0
        simpa [Matrix.mulVec, dotProduct] using this
    have h0 : ext mu = 0 :=
      hmin _ hrel (fun i hzi => hext_out mu i (fun hSi => (mem_supp.mp hSi) hzi))
    funext k
    rw [← hext_sg mu k, h0]
    rfl
  have hsle : S.card ≤ n + 1 := by
    have hli : Function.Injective (Mr.mulVecLin) := by
      intro u v huv
      simp only [Matrix.mulVecLin_apply] at huv
      have h0 : Mr.mulVec (u - v) = 0 := by
        rw [Matrix.mulVec_sub, huv, sub_self]
      exact sub_eq_zero.mp (hinj _ h0)
    have h := LinearMap.finrank_le_finrank_of_injective hli
    simpa using h
  -- 6. an invertible square subsystem
  obtain ⟨r, w, row, col, hw1, hrs, hdet, hsq, hw0⟩ :=
    SmaleNinth.exists_square_subsystem Mr (fun rr => ((tgt n rr : ℤ) : ℝ)) Finset.univ zz
      (fun i _ => by rw [hMeq])
  have hw : w = zz := by
    have h0 : Mr.mulVec (w - zz) = 0 := by
      funext rr
      have h1 : Mr.mulVec w rr = ((tgt n rr : ℤ) : ℝ) := hw1 rr (Finset.mem_univ rr)
      have h2 : Mr.mulVec zz rr = ((tgt n rr : ℤ) : ℝ) := by rw [hMeq]
      rw [Matrix.mulVec_sub]
      simp [h1, h2]
    exact sub_eq_zero.mp (hinj _ h0)
  subst hw
  have hsurj : Function.Surjective col := by
    intro k
    by_contra hk
    exact hznz k (hw0 k hk)
  have hsr : S.card ≤ r := by
    have h := Fintype.card_le_of_surjective col hsurj
    simpa using h
  have hrEq : r = S.card := le_antisymm hrs hsr
  have hbij : Function.Bijective col :=
    (Fintype.bijective_iff_surjective_and_card col).mpr ⟨hsurj, by simp [hrEq]⟩
  have hrle : r ≤ n + 1 := le_trans hrs hsle
  -- 7. Cramer's rule on the square subsystem
  set N : Matrix (Fin r) (Fin r) ℤ := M.submatrix row col with hN
  set v : Fin r → ℤ := fun k => tgt n (row k) with hv
  have hNmap : Mr.submatrix row col = N.map (Int.cast : ℤ → ℝ) := rfl
  have hDr : ((N.det : ℤ) : ℝ) ≠ 0 := by
    rw [← det_map_cast N, ← hNmap]; exact hdet
  have hD : N.det ≠ 0 := by
    intro h; apply hDr; rw [h]; simp
  have hsq' : (N.map (Int.cast : ℤ → ℝ)).mulVec (fun k => zz (col k))
      = fun k => ((v k : ℤ) : ℝ) := by
    rw [← hNmap]; exact hsq
  have hcram : (N.map (Int.cast : ℤ → ℝ)).cramer (fun k => ((v k : ℤ) : ℝ))
      = ((N.map (Int.cast : ℤ → ℝ)).det) • (fun k => zz (col k)) := by
    have h1 := Matrix.mulVec_cramer (N.map (Int.cast : ℤ → ℝ)) (fun k => ((v k : ℤ) : ℝ))
    have h2 : (N.map (Int.cast : ℤ → ℝ)).mulVec
        (((N.map (Int.cast : ℤ → ℝ)).det) • (fun k => zz (col k)))
        = (N.map (Int.cast : ℤ → ℝ)).det • (fun k => ((v k : ℤ) : ℝ)) := by
      rw [Matrix.mulVec_smul, hsq']
    have h3 : (N.map (Int.cast : ℤ → ℝ)).mulVec
        ((N.map (Int.cast : ℤ → ℝ)).cramer (fun k => ((v k : ℤ) : ℝ))
          - ((N.map (Int.cast : ℤ → ℝ)).det) • (fun k => zz (col k))) = 0 := by
      rw [Matrix.mulVec_sub, h1, h2, sub_self]
    have h4 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_map_cast]; exact hDr) h3
    exact sub_eq_zero.mp h4
  have hgk : ∀ k : Fin r,
      (((N.updateCol k v).det : ℤ) : ℝ) = ((N.det : ℤ) : ℝ) * zz (col k) := by
    intro k
    have h := congrFun hcram k
    rw [Matrix.cramer_apply, map_updateCol, det_map_cast, det_map_cast] at h
    simpa using h
  -- 8. the integral certificate
  obtain ⟨eps, heps⟩ : ∃ e : ℤ, e = if 0 < N.det then 1 else -1 := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Fin r → ℤ, G = fun k => eps * (N.updateCol k v).det := ⟨_, rfl⟩
  have hepsD : eps * N.det = |N.det| := by
    rcases lt_trichotomy 0 N.det with h | h | h
    · rw [heps, if_pos h, one_mul, abs_of_pos h]
    · exact absurd h.symm hD
    · rw [heps, if_neg (not_lt.mpr (le_of_lt h)), abs_of_neg h]; ring
  have hepsabs : |eps| = 1 := by rw [heps]; split <;> simp
  have habsD : (1 : ℤ) ≤ |N.det| := by
    have h := abs_pos.mpr hD
    omega
  have hGR : ∀ k, ((G k : ℤ) : ℝ) = ((|N.det| : ℤ) : ℝ) * zz (col k) := by
    intro k
    have h := hgk k
    have h2 : ((G k : ℤ) : ℝ) = ((eps : ℤ) : ℝ) * (((N.updateCol k v).det : ℤ) : ℝ) := by
      rw [hGdef]; push_cast; ring
    rw [h2, h, ← mul_assoc]
    congr 1
    rw [← hepsD]
    push_cast
    ring
  have hzznn : ∀ k, 0 ≤ zz (col k) := fun k => hz.1 (sg (col k))
  have hGnn : ∀ k, 0 ≤ G k := by
    intro k
    have h : (0 : ℝ) ≤ ((G k : ℤ) : ℝ) := by
      rw [hGR k]
      exact mul_nonneg (by positivity) (hzznn k)
    exact_mod_cast h
  have hdetbound : ∀ k : Fin r,
      |(N.updateCol k v).det| ≤ ((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1) := by
    intro k
    have hent : ∀ i j, |(N.updateCol k v) i j| ≤ (U : ℤ) := by
      intro i j
      by_cases h : j = k
      · rw [Matrix.updateCol_apply, if_pos h]
        simp only [hv]
        exact tgt_entry_bound n U hU (row i)
      · rw [Matrix.updateCol_apply, if_neg h]
        simp only [hN, Matrix.submatrix_apply, hM]
        exact colMat_entry_bound A b sg U hA hb (row i) (col j)
    have h1 := SmaleNinth.abs_det_le_factorial_mul_pow U (N.updateCol k v) hent
    have hf : (r.factorial : ℤ) ≤ ((n + 1).factorial : ℤ) := by
      exact_mod_cast Nat.factorial_le hrle
    have hp : (U : ℤ) ^ r ≤ (U : ℤ) ^ (n + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hU) hrle
    have hUr : (0 : ℤ) ≤ (U : ℤ) ^ r := by positivity
    have hfn : (0 : ℤ) ≤ ((n + 1).factorial : ℤ) := by positivity
    calc |(N.updateCol k v).det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := h1
      _ ≤ ((n + 1).factorial : ℤ) * (U : ℤ) ^ r := mul_le_mul_of_nonneg_right hf hUr
      _ ≤ ((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1) := mul_le_mul_of_nonneg_left hp hfn
  have hGle : ∀ k, G k ≤ ((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1) := by
    intro k
    have habs : |G k| = |(N.updateCol k v).det| := by
      rw [hGdef]; simp [abs_mul, hepsabs]
    calc G k ≤ |G k| := le_abs_self _
      _ = |(N.updateCol k v).det| := habs
      _ ≤ _ := hdetbound k
  refine ⟨fun i => ∑ k : Fin r, if sg (col k) = i then G k else 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg (fun k _ => by by_cases h : sg (col k) = i <;> simp [h, hGnn k])
  · intro j
    rw [sum_swap_ite (fun k => sg (col k)) G (fun i => A i j)]
    have hbijsum : ∑ k : Fin r, zz (col k) * Ar (sg (col k)) j
        = ∑ k : Fin S.card, zz k * Ar (sg k) j :=
      Fintype.sum_bijective col hbij _ _ (fun k => rfl)
    have hR : ((∑ k : Fin r, G k * A (sg (col k)) j : ℤ) : ℝ) = 0 := by
      push_cast
      have hstep : ∀ k : Fin r, ((G k : ℤ) : ℝ) * ((A (sg (col k)) j : ℤ) : ℝ)
          = ((|N.det| : ℤ) : ℝ) * (zz (col k) * Ar (sg (col k)) j) := by
        intro k
        rw [hGR k, hArval]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, hbijsum,
        ← hreidx (fun i => z i * Ar i j) (fun i hi => by rw [hzout i hi]; ring),
        hz.2.1 j, mul_zero]
    exact_mod_cast hR
  · rw [sum_swap_ite (fun k => sg (col k)) G b]
    have hbijsum : ∑ k : Fin r, zz (col k) * br (sg (col k))
        = ∑ k : Fin S.card, zz k * br (sg k) :=
      Fintype.sum_bijective col hbij _ _ (fun k => rfl)
    have hR : ((∑ k : Fin r, G k * b (sg (col k)) : ℤ) : ℝ) = ((|N.det| : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      have hstep : ∀ k : Fin r, ((G k * b (sg (col k)) : ℤ) : ℝ)
          = ((|N.det| : ℤ) : ℝ) * (zz (col k) * br (sg (col k))) := by
        intro k
        rw [Int.cast_mul, hGR k]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, hbijsum,
        ← hreidx (fun i => z i * br i) (fun i hi => by rw [hzout i hi]; ring),
        hz.2.2, mul_one]
    have hZ : (∑ k : Fin r, G k * b (sg (col k)) : ℤ) = |N.det| := by exact_mod_cast hR
    rw [hZ]
    exact habsD
  · rw [sum_swap_ite' (fun k => sg (col k)) G]
    calc ∑ k : Fin r, G k
        ≤ ∑ _k : Fin r, ((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1) :=
          Finset.sum_le_sum (fun k _ => hGle k)
      _ = (r : ℤ) * (((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1)) := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ ((n + 1 : ℕ) : ℤ) * (((n + 1).factorial : ℤ) * (U : ℤ) ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hrle
      _ = ((n + 1) * (n + 1).factorial * U ^ (n + 1) : ℤ) := by push_cast; ring


end FarkasCert

/-- **An infeasible integer system has an integral Farkas certificate of
bounded `ℓ¹` norm.** -/
theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hempty : polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) = ∅) :
    ∃ y : Fin m → ℤ, (∀ i, 0 ≤ y i) ∧
      (∀ j, ∑ i, y i * A i j = 0) ∧
      1 ≤ ∑ i, y i * b i ∧
      (∑ i, y i) ≤ ((n + 1) * (n + 1).factorial * U ^ (n + 1) : ℤ) :=
  FarkasCert.main U hU hn A b hA hb hempty
