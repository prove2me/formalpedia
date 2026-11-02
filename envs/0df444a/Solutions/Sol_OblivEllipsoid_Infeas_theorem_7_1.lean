-- Prove2me | solution 1 for OblivEllipsoid.Infeas.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:40:15.043144+00:00
-- url     : https://prove2.me/submissions/571f7a69-fb59-4ecb-8544-bc8906217561

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model
import Theorems.Thm_OblivEllipsoid_Infeas_remark_1_1
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_1
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_3
import Theorems.Thm_OblivEllipsoid_Infeas_theorem_6_1
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_7_1
import Theorems.Thm_OblivEllipsoid_Infeas_lemma_7_1
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_4_1_b
import Theorems.Thm_OblivEllipsoid_Infeas_lemma_6_2_a

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAThm71

variable {n m : ℕ}

lemma B_smul (A : Matrix (Fin n) (Fin m) ℝ) (c : ℝ) (d : Fin m → ℝ) :
    B A (c • d) = c • B A d := by
  simp [B, Matrix.diagonal_smul]

lemma inv_smul_any (M : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : c ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · exact Matrix.inv_eq_left_inv (by simp [smul_smul, hc, Matrix.nonsing_inv_mul _ h])
  · have h2 : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0; apply hu; rw [h0, mul_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h2, smul_zero]

lemma y_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    y A u (c • d) ell = y A u d ell := by
  unfold y
  rw [B_smul, inv_smul_any _ hc]
  have : (c • d) * r u ell = c • (d * r u ell) := by
    funext i; simp [mul_assoc]
  rw [this, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

lemma t_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    t A u (c • d) ell = t A u d ell := by
  unfold t; rw [y_smul A u d ell hc]

lemma f_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    f A u (c • d) ell = c * f A u d ell := by
  unfold f
  rw [t_smul A u d ell hc, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [mul_assoc]

lemma slab_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0)
    (i : Fin m) : slabRadius A u (c • d) ell i = slabRadius A u d ell i := by
  unfold slabRadius
  rw [f_smul A u d ell hc, B_smul, inv_smul_any _ hc, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  congr 1
  field_simp

lemma Lb_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0)
    (i : Fin m) : Lb A u (c • d) ell i = Lb A u d ell i := by
  unfold Lb; rw [y_smul A u d ell hc, slab_smul A u d ell hc]

lemma certLB_iff (A : Matrix (Fin n) (Fin m) ℝ) (u ell : Fin m → ℝ)
    (Lam : Matrix (Fin m) (Fin m) ℝ) :
    CertLB A u ell Lam ↔ ∀ k, CertLBi A u k (ell k) (Lam.col k) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ k
    refine ⟨?_, fun i => h2 i k, ?_⟩
    · funext r
      have := congrFun (congrFun h1 r) k
      simp only [Matrix.mul_apply, Matrix.neg_apply] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Pi.neg_apply, col]
      rw [this]
    · have := h3 k
      simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
      simp only [dotProduct, Matrix.col_apply]
      exact this
  · intro h
    refine ⟨?_, fun i k => (h k).2.1 i, ?_⟩
    · ext r k
      have := congrFun (h k).1 r
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Pi.neg_apply, col] at this
      simp only [Matrix.mul_apply, Matrix.neg_apply]
      rw [this]
    · intro k
      have := (h k).2.2
      simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      simp only [dotProduct, Matrix.col_apply] at this
      exact this

lemma certLBi_mono {A : Matrix (Fin n) (Fin m) ℝ} {u : Fin m → ℝ} {k : Fin m} {l l' : ℝ}
    {w : Fin m → ℝ} (h : CertLBi A u k l w) (hl : l' ≤ l) : CertLBi A u k l' w :=
  ⟨h.1, h.2.1, hl.trans h.2.2⟩

/-- The certificate matrix after the (conditional) column replacement of Steps 5-8. -/
lemma certLB_update (A : Matrix (Fin n) (Fin m) ℝ) (u ell : Fin m → ℝ)
    (Lam : Matrix (Fin m) (Fin m) ℝ) (hcert : CertLB A u ell Lam) (j : Fin m) (L : ℝ)
    (w : Fin m → ℝ) (hw : CertLBi A u j L w) (ell' : Fin m → ℝ)
    (hother : ∀ k, k ≠ j → ell' k ≤ ell k) (hj : ell' j ≤ max (ell j) L) :
    CertLB A u ell' (if ell j < L then replaceColumn Lam j w else Lam) ∧
    CertLBi A u j (max (ell j) L) ((if ell j < L then replaceColumn Lam j w else Lam).col j) := by
  have hc := (certLB_iff A u ell Lam).1 hcert
  have hcolj : CertLBi A u j (max (ell j) L)
      ((if ell j < L then replaceColumn Lam j w else Lam).col j) := by
    split_ifs with h
    · have : (replaceColumn Lam j w).col j = w := by
        funext r; simp [replaceColumn, Matrix.col_apply]
      rw [this, max_eq_right h.le]; exact hw
    · rw [max_eq_left (not_lt.1 h)]; exact hc j
  refine ⟨?_, hcolj⟩
  rw [certLB_iff]
  intro k
  by_cases hk : k = j
  · subst hk; exact certLBi_mono hcolj hj
  · have : (if ell j < L then replaceColumn Lam j w else Lam).col k = Lam.col k := by
      split_ifs
      · funext r; simp [replaceColumn, Matrix.col_apply, hk]
      · rfl
    rw [this]; exact certLBi_mono (hc k) (hother k hk)

lemma AT_mulVec_apply (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (k : Fin m) :
    (Aᵀ *ᵥ x) k = col A k ⬝ᵥ x := by
  simp [Matrix.mulVec, dotProduct, col, Matrix.transpose_apply]

lemma exists_viol {A : Matrix (Fin n) (Fin m) ℝ} {u : Fin m → ℝ} {x : Fin n → ℝ}
    (h : ¬ IsFeasible A u x) : ∃ i, 0 < col A i ⬝ᵥ x - u i := by
  unfold IsFeasible at h
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [AT_mulVec_apply] at hi; linarith⟩

lemma ell1_other (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j k : Fin m)
    (hk : k ≠ j) : ell1 A u d ell j k = ell k := by
  simp [ell1, Pi.single_eq_of_ne hk]

lemma ell2_other (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j k : Fin m)
    (hk : k ≠ j) : ell2 A u d ell j k = ell k := by
  simp [ell2, Pi.single_eq_of_ne hk, ell1_other A u d ell j k hk]

lemma t_sub_v (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m) :
    t A u d ell j - v u ell j = col A j ⬝ᵥ y A u d ell - u j := by
  simp only [t, v, r, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, AT_mulVec_apply]
  ring

lemma ell1_le (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m)
    (hviol : 0 < col A j ⬝ᵥ y A u d ell - u j) (hdj : 0 ≤ d j) :
    ell1 A u d ell j j ≤ ell j := by
  simp only [ell1, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [t_sub_v]
  have : 0 ≤ 2 * (col A j ⬝ᵥ y A u d ell - u j) / (d j * slabRadius A u d ell j ^ 2) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- The most violated constraint is violated by at least `τ(A,u)`. -/
lemma tau_le_viol (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) (x : Fin n → ℝ) (j : Fin m)
    (hmax : ∀ i : Fin m, col A i ⬝ᵥ x - u i ≤ col A j ⬝ᵥ x - u j) :
    tau A u ≤ col A j ⬝ᵥ x - u j := by
  have hz := (proposition_4_1_b A u hA hinf).1
  have hbdd : BddAbove (Set.range fun x : Fin n → ℝ => ⨅ i : Fin m, (u i - col A i ⬝ᵥ x)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    obtain ⟨i, hi⟩ := exists_viol (fun h => hinf ⟨z, h⟩)
    have := ciInf_le (Finite.bddBelow_range fun i : Fin m => (u i - col A i ⬝ᵥ z)) i
    simp only at this ⊢
    linarith
  have h1 : (⨅ i : Fin m, (u i - col A i ⬝ᵥ x)) ≤ zStar A u :=
    le_csSup hbdd ⟨x, rfl⟩
  have : Nonempty (Fin m) := ⟨j⟩
  have h2 : u j - col A j ⬝ᵥ x ≤ ⨅ i : Fin m, (u i - col A i ⬝ᵥ x) :=
    le_ciInf fun i => by have := hmax i; linarith
  rw [hz]; linarith

/-- One completed update of Algorithm 4 (Steps 3-12) preserves positivity of `d` and the
certified lower bounds, and decreases the potential. -/
lemma step (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) (s s' : State m)
    (hd : ∀ i, 0 < s.d i) (hc : CertLB A u s.ell s.Lam)
    (h : OEAIter A u s (.next s')) :
    (∀ i, 0 < s'.d i) ∧ CertLB A u s'.ell s'.Lam ∧
      potential A u s'.d s'.ell ≤
        Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u s.d s.ell ∧
      0 < f A u s.d s.ell ∧
      ∃ j, tau A u ≤ (s.d j / f A u s.d s.ell) ^ (-(1 / 2 : ℝ)) := by
  rcases h with ⟨_, h⟩ | ⟨_, _, lam, _, h⟩ | ⟨hinfeas, hfpos, j, hmax, hrest⟩
  · cases h
  · cases h
  set F := f A u s.d s.ell with hF
  set dd := (1 / F) • s.d with hdd
  have hc0 : (1 / F) ≠ 0 := by positivity
  have hddpos : ∀ i, 0 < dd i := fun i => by
    simp only [hdd, Pi.smul_apply, smul_eq_mul]; have := hd i; positivity
  have hfdd : f A u dd s.ell = 1 := by
    rw [hdd, f_smul A u s.d s.ell hc0, ← hF]; field_simp
  have hydd : y A u dd s.ell = y A u s.d s.ell := y_smul A u s.d s.ell hc0
  have hslab : slabRadius A u dd s.ell j = slabRadius A u s.d s.ell j :=
    slab_smul A u s.d s.ell hc0 j
  simp only at hrest
  rcases hrest with ⟨_, h⟩ | ⟨hLj, hP⟩
  · cases h
  unfold Proc3 at hP
  simp only at hP
  rcases hP with ⟨_, h⟩ | ⟨_, _, lam, _, h⟩ | ⟨_, hf1, h⟩
  · cases h
  · cases h
  injection h with h
  subst h
  simp only
  -- basic facts at the normalized weights
  obtain ⟨i0, hi0⟩ := exists_viol hinfeas
  have hviol : 0 < col A j ⬝ᵥ y A u dd s.ell - u j := by
    have := hmax i0; rw [hydd] at this ⊢; linarith
  have hle : col A j ⬝ᵥ y A u dd s.ell - u j ≤ slabRadius A u dd s.ell j := by
    simp only [Lb] at hLj; linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast j.pos
  -- Theorem 6.1
  obtain ⟨α, hα, hd3⟩ := theorem_6_1 A u dd s.ell s.Lam hA hddpos hc hfdd j hviol hle hf1
  have hαpos : 0 < α := lt_of_le_of_lt (by apply div_nonneg <;> nlinarith) hα
  have hcoef : 0 ≤ (2 / ((m : ℝ) - 1)) * (1 / slabRadius A u dd s.ell j ^ 2) := by
    apply mul_nonneg
    · apply div_nonneg <;> linarith
    · positivity
  have hd3pos : ∀ i, 0 < d3 A u dd s.ell j i := by
    intro i
    rw [hd3]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 := hddpos i
    have h2 : (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : Fin m → ℝ) i := by
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij]
    have := mul_nonneg hcoef h2
    positivity
  -- normalization of the new weights
  have hf3 : f A u (d3 A u dd s.ell j) (ell2 A u dd s.ell j) = 1 := by
    set F2 := f A u (d2 A u dd s.ell j) (ell2 A u dd s.ell j) with hF2
    have hd3def : d3 A u dd s.ell j = (1 / F2) • d2 A u dd s.ell j := rfl
    by_cases h0 : F2 = 0
    · exfalso
      have := hd3pos j
      rw [hd3def, h0] at this
      simp at this
    · rw [hd3def, f_smul _ _ _ _ (by positivity : (1 / F2) ≠ 0), ← hF2]
      field_simp
  refine ⟨hd3pos, ?_, ?_, hfpos, ?_⟩
  · -- certified lower bounds
    have h51 := proposition_5_1 A u dd s.ell s.Lam hA hddpos hc hfdd j
    have h62 := lemma_6_2_a A u dd s.ell s.Lam hA hddpos hc hfdd j hviol hle hf1
    exact (certLB_update A u s.ell s.Lam hc j (Lb A u dd s.ell j) _ h51 _
      (fun k hk => le_of_eq (ell2_other A u dd s.ell j k hk)) h62).1
  · -- potential decrease (Lemma 7.1)
    have htau : tau A u ≤ (s.d j / F) ^ (-(1 / 2 : ℝ)) := by
      have h1 := tau_le_viol A u hA hinf (y A u dd s.ell) j (fun i => by
        have := hmax i; rwa [hydd] at this ⊢)
      have h2 := proposition_7_1 A u s.d s.ell hA hd hfpos j
      rw [hslab] at hle
      linarith
    apply lemma_7_1 A u s.d s.ell _ _ hA hd hd3pos hfpos (by rw [hf3]; norm_num) j α
    · rw [hf3, div_one, one_smul, hd3, hslab]
    · exact hα.le
    · exact htau
  · refine ⟨j, ?_⟩
    have h1 := tau_le_viol A u hA hinf (y A u dd s.ell) j (fun i => by
      have := hmax i; rwa [hydd] at this ⊢)
    have h2 := proposition_7_1 A u s.d s.ell hA hd hfpos j
    rw [hslab] at hle
    linarith

/-- From every state with positive weights and certified lower bounds, Algorithm 4 can make a
full pass, and every certificate it may return solves (Alt), and it never returns a solution. -/
lemma pass (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) (s : State m)
    (hd : ∀ i, 0 < s.d i) (hc : CertLB A u s.ell s.Lam) :
    (∃ o, OEAIter A u s o) ∧ (∀ lam, OEAIter A u s (.certificate lam) → IsAlt A u lam) ∧
      (∀ x, ¬ OEAIter A u s (.solution x)) := by
  set F := f A u s.d s.ell with hF
  set dd := (1 / F) • s.d with hdd
  refine ⟨?_, ?_, ?_⟩
  · -- existence of a pass
    by_cases hfeas : IsFeasible A u (y A u s.d s.ell)
    · exact ⟨_, Or.inl ⟨hfeas, rfl⟩⟩
    by_cases hf0 : F ≤ 0
    · obtain ⟨out, hout⟩ := (proposition_5_3 A u s.d s.ell s.Lam hA hd hc hf0 hfeas).1
      exact ⟨_, Or.inr (Or.inl ⟨hfeas, hf0, out, hout, rfl⟩)⟩
    push Not at hf0
    have hc0 : (1 / F) ≠ 0 := by positivity
    have hddpos : ∀ i, 0 < dd i := fun i => by
      simp only [hdd, Pi.smul_apply, smul_eq_mul]; have := hd i; positivity
    have hydd : y A u dd s.ell = y A u s.d s.ell := y_smul A u s.d s.ell hc0
    obtain ⟨i0, hi0⟩ := exists_viol hfeas
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i => col A i ⬝ᵥ y A u dd s.ell - u i) ⟨i0, Finset.mem_univ _⟩
    have hmax : ∀ i, col A i ⬝ᵥ y A u dd s.ell - u i ≤ col A j ⬝ᵥ y A u dd s.ell - u j :=
      fun i => hj i (Finset.mem_univ _)
    set Lj := Lb A u dd s.ell j with hLj
    set Lam' := if s.ell j < Lj then
        replaceColumn s.Lam j (lamTilde A u dd s.ell s.Lam j) else s.Lam with hLam'
    by_cases hcert : u j < Lj
    · exact ⟨_, Or.inr (Or.inr ⟨hfeas, hf0, j, hmax, Or.inl ⟨hcert, rfl⟩⟩)⟩
    push Not at hcert
    have hfdd : f A u dd s.ell = 1 := by
      rw [hdd, f_smul A u s.d s.ell hc0, ← hF]; field_simp
    have hviol : 0 < col A j ⬝ᵥ y A u dd s.ell - u j := by
      have := hmax i0; rw [hydd] at this ⊢; linarith
    set e1 := ell1 A u dd s.ell j with he1
    by_cases hfeas1 : IsFeasible A u (y A u dd e1)
    · exact ⟨_, Or.inr (Or.inr ⟨hfeas, hf0, j, hmax, Or.inr ⟨hcert, Or.inl ⟨hfeas1, rfl⟩⟩⟩)⟩
    by_cases hf1 : f A u dd e1 ≤ 0
    · have h51 := proposition_5_1 A u dd s.ell s.Lam hA hddpos hc hfdd j
      have hcert1 : CertLB A u e1 Lam' :=
        (certLB_update A u s.ell s.Lam hc j Lj _ h51 e1
          (fun k hk => le_of_eq (ell1_other A u dd s.ell j k hk))
          ((ell1_le A u dd s.ell j hviol (hddpos j).le).trans (le_max_left _ _))).1
      obtain ⟨out, hout⟩ := (proposition_5_3 A u dd e1 Lam' hA hddpos hcert1 hf1 hfeas1).1
      exact ⟨_, Or.inr (Or.inr ⟨hfeas, hf0, j, hmax, Or.inr ⟨hcert,
        Or.inr (Or.inl ⟨hfeas1, hf1, out, hout, rfl⟩)⟩⟩)⟩
    push Not at hf1
    exact ⟨_, Or.inr (Or.inr ⟨hfeas, hf0, j, hmax, Or.inr ⟨hcert,
        Or.inr (Or.inr ⟨hfeas1, hf1, rfl⟩)⟩⟩)⟩
  · -- every certificate solves (Alt)
    intro lam h
    rcases h with ⟨_, h⟩ | ⟨hfeas, hf0, out, hout, h⟩ | ⟨hfeas, hfpos, j, hmax, hrest⟩
    · cases h
    · cases h
      exact (proposition_5_3 A u s.d s.ell s.Lam hA hd hc hf0 hfeas).2 _ hout
    rw [← hF] at hfpos hmax hrest
    rw [← hdd] at hmax hrest
    have hc0 : (1 / F) ≠ 0 := by positivity
    have hddpos : ∀ i, 0 < dd i := fun i => by
      simp only [hdd, Pi.smul_apply, smul_eq_mul]; have := hd i; positivity
    have hydd : y A u dd s.ell = y A u s.d s.ell := y_smul A u s.d s.ell hc0
    have hfdd : f A u dd s.ell = 1 := by
      rw [hdd, f_smul A u s.d s.ell hc0, ← hF]; field_simp
    have h51 := proposition_5_1 A u dd s.ell s.Lam hA hddpos hc hfdd j
    simp only at hrest
    rcases hrest with ⟨hgap, h⟩ | ⟨hLj, hP⟩
    · cases h
      have hcol := (certLB_update A u s.ell s.Lam hc j _ _ h51 s.ell
        (fun k _ => le_rfl) (le_max_left _ _)).2
      exact (remark_1_1 A u hA j _ _ hcol (lt_of_lt_of_le hgap (le_max_right _ _))).2
    unfold Proc3 at hP
    simp only at hP
    rcases hP with ⟨_, h⟩ | ⟨hfeas1, hf1, out, hout, h⟩ | ⟨_, _, h⟩
    · cases h
    · cases h
      obtain ⟨i0, hi0⟩ := exists_viol hfeas
      have hviol : 0 < col A j ⬝ᵥ y A u dd s.ell - u j := by
        have := hmax i0; rw [hydd] at this ⊢; linarith
      have hcert1 := (certLB_update A u s.ell s.Lam hc j _ _ h51 (ell1 A u dd s.ell j)
          (fun k hk => le_of_eq (ell1_other A u dd s.ell j k hk))
          ((ell1_le A u dd s.ell j hviol (hddpos j).le).trans (le_max_left _ _))).1
      exact (proposition_5_3 A u dd _ _ hA hddpos hcert1 hf1 hfeas1).2 _ hout
    · cases h
  · -- no solution is ever returned
    intro x h
    rcases h with ⟨hfeas, _⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, j, _, hrest⟩
    · exact hinf ⟨_, hfeas⟩
    · cases h
    simp only at hrest
    rcases hrest with ⟨_, h⟩ | ⟨_, hP⟩
    · cases h
    unfold Proc3 at hP
    simp only at hP
    rcases hP with ⟨hfeas1, _⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩
    · exact hinf ⟨_, hfeas1⟩
    · cases h
    · cases h

lemma rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- The bound `φ(e,ℓ) ≤ (‖u-ℓ‖/2)^m` from the proof of Theorem 7.1. -/
lemma potential_init (A : Matrix (Fin n) (Fin m) ℝ) (u ell : Fin m → ℝ)
    (hf : 0 < f A u (fun _ => 1) ell)
    (htau : tau A u ≤ (1 / f A u (fun _ => 1) ell) ^ (-(1 / 2 : ℝ))) :
    potential A u (fun _ => 1) ell ≤
      (Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / 2) ^ m := by
  set f0 := f A u (fun _ => 1) ell with hf0
  set W := Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) with hW
  have hX : 0 ≤ ∑ i : Fin m, (u i - ell i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW2 : (W / 2) ^ 2 = (∑ i : Fin m, (u i - ell i) ^ 2) / 4 := by
    rw [div_pow, hW, Real.sq_sqrt hX]; norm_num
  have hsq : (1 / f0) ^ (-(1 / 2 : ℝ)) = Real.sqrt f0 := by
    rw [rpow_neg_half (by positivity), one_div, Real.sqrt_inv, inv_inv]
  have hf0le : f0 ≤ (∑ i : Fin m, (u i - ell i) ^ 2) / 4 := by
    have h1 : f0 = (∑ i : Fin m, 1 * (v u ell i) ^ 2) - ∑ i : Fin m, 1 * (t A u (fun _ => 1) ell i) ^ 2 := rfl
    have h2 : 0 ≤ ∑ i : Fin m, 1 * (t A u (fun _ => 1) ell i) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    have h3 : (∑ i : Fin m, 1 * (v u ell i) ^ 2) = (∑ i : Fin m, (u i - ell i) ^ 2) / 4 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [v, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    linarith
  have hsqrt : Real.sqrt f0 ≤ W / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, by rw [hW2]; exact hf0le⟩
  have hτ0 : 0 ≤ tau A u := abs_nonneg _
  have hκ : ((m : ℝ) / ((m : ℝ) + 1)) * tau A u ≤ tau A u := by
    have : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  unfold potential
  rw [show ∀ c : ℝ, c ^ m = ∏ _i : Fin m, c from fun c => by simp]
  apply Finset.prod_le_prod
  · intro i _
    exact le_max_of_le_right (by positivity)
  · intro i _
    simp only [mu]
    rw [hsq]
    apply max_le hsqrt
    rw [← hsq] at hsqrt
    linarith

lemma potential_lower (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) :
    (((m : ℝ) / ((m : ℝ) + 1)) * tau A u) ^ m ≤ potential A u d ell := by
  have hτ0 : 0 ≤ tau A u := abs_nonneg _
  unfold potential
  rw [show ∀ c : ℝ, c ^ m = ∏ _i : Fin m, c from fun c => by simp]
  exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => le_max_right _ _)

lemma invariant (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (hA : Assumption11 A)
    (ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hcert : CertLB A u ell Lam) (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    ∀ k s, Reach A u ⟨fun _ => 1, ell, Lam⟩ k s →
      (∀ i, 0 < s.d i) ∧ CertLB A u s.ell s.Lam ∧
      (k = 0 → s = ⟨fun _ => 1, ell, Lam⟩) ∧
      (1 ≤ k → potential A u s.d s.ell ≤
        Real.exp (-((k : ℝ) / (2 * ((m : ℝ) + 1)))) *
          (Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / 2) ^ m) := by
  intro k s h
  induction h with
  | zero => exact ⟨fun _ => one_pos, hcert, fun _ => rfl, fun h => absurd h (by norm_num)⟩
  | @succ k s s' hR hstep ih =>
    obtain ⟨hd, hc, h0, hpot⟩ := ih
    obtain ⟨hd', hc', hdec, hfpos, j, htau⟩ := step A u hA hinf s s' hd hc hstep
    refine ⟨hd', hc', fun h => absurd h (Nat.succ_ne_zero k), fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hs := h0 rfl
      subst hs
      have hinit := potential_init A u ell hfpos htau
      calc potential A u s'.d s'.ell
          ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u (fun _ => 1) ell := hdec
        _ ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) *
              (Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / 2) ^ m := by
            gcongr
        _ = _ := by norm_num
    · have := hpot hk
      calc potential A u s'.d s'.ell
          ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u s.d s.ell := hdec
        _ ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * (Real.exp (-((k : ℝ) / (2 * ((m : ℝ) + 1)))) *
              (Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / 2) ^ m) := by gcongr
        _ = _ := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring

theorem thm71 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hcert : CertLB A u ell Lam)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    let s0 : State m := ⟨fun _ => 1, ell, Lam⟩
    (∀ k s, Reach A u s0 k s → ∃ o, OEAIter A u s o) ∧
    (∀ k s lam, Reach A u s0 k s →
      OEAIter A u s (.certificate lam) → IsAlt A u lam) ∧
    (∀ k s x, Reach A u s0 k s → ¬ OEAIter A u s (.solution x)) ∧
    (∀ k s, Reach A u s0 k s → 1 ≤ k →
      (k : ℤ) ≤ ⌊2 * (m : ℝ) * ((m : ℝ) + 1) *
        Real.log (((m : ℝ) + 1) / (2 * (m : ℝ)) *
          Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / tau A u)⌋) := by
  intro s0
  have hinv := invariant A u hA ell Lam hcert hinf
  refine ⟨fun k s h => ?_, fun k s lam h => ?_, fun k s x h => ?_, fun k s h hk => ?_⟩
  · obtain ⟨hd, hc, -, -⟩ := hinv k s h
    exact (pass A u hA hinf s hd hc).1
  · obtain ⟨hd, hc, -, -⟩ := hinv k s h
    exact (pass A u hA hinf s hd hc).2.1 lam
  · obtain ⟨hd, hc, -, -⟩ := hinv k s h
    exact (pass A u hA hinf s hd hc).2.2 x
  · obtain ⟨-, -, -, hpot⟩ := hinv k s h
    have hup := hpot hk
    have hlow := potential_lower A u s.d s.ell
    have hτ := (proposition_4_1_b A u hA hinf).2.1
    set W := Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) with hW
    set E := (k : ℝ) / (2 * ((m : ℝ) + 1)) with hE
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hW0 : 0 ≤ W := Real.sqrt_nonneg _
    have hchain : (((m : ℝ) / ((m : ℝ) + 1)) * tau A u) ^ m ≤ Real.exp (-E) * (W / 2) ^ m :=
      hlow.trans hup
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      subst hm
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_add] at hchain
      have : -E < 0 := by rw [hE]; simp only [Nat.cast_zero, zero_add, mul_one] at *; 
                          apply neg_neg_of_pos; positivity
      have := Real.exp_lt_one_iff.2 this
      linarith
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    set κ := ((m : ℝ) / ((m : ℝ) + 1)) * tau A u with hκ
    have hκpos : 0 < κ := by positivity
    have hκm : 0 < κ ^ m := pow_pos hκpos m
    have hWpos : 0 < W / 2 := by
      rcases (div_nonneg hW0 (by norm_num : (0:ℝ) ≤ 2)).eq_or_lt with h0 | h0
      · exfalso
        rw [← h0, zero_pow (by omega), mul_zero] at hchain
        linarith
      · exact h0
    have hlog := Real.log_le_log hκm hchain
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hWpos m).ne', Real.log_exp,
      Real.log_pow, Real.log_pow] at hlog
    have hratio : ((m : ℝ) + 1) / (2 * (m : ℝ)) * W / tau A u = (W / 2) / κ := by
      rw [hκ]; field_simp
    rw [Int.le_floor, hratio, Real.log_div hWpos.ne' hκpos.ne']
    push_cast
    have hE' : (k : ℝ) = 2 * ((m : ℝ) + 1) * E := by rw [hE]; field_simp
    rw [hE']
    have : E ≤ (m : ℝ) * (Real.log (W / 2) - Real.log κ) := by nlinarith
    have h2 : 0 < 2 * ((m : ℝ) + 1) := by positivity
    nlinarith

end OEAThm71
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hcert : CertLB A u ell Lam)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    let s0 : State m := ⟨fun _ => 1, ell, Lam⟩
    (∀ k s, Reach A u s0 k s → ∃ o, OEAIter A u s o) ∧
    (∀ k s lam, Reach A u s0 k s →
      OEAIter A u s (.certificate lam) → IsAlt A u lam) ∧
    (∀ k s x, Reach A u s0 k s → ¬ OEAIter A u s (.solution x)) ∧
    (∀ k s, Reach A u s0 k s → 1 ≤ k →
      (k : ℤ) ≤ ⌊2 * (m : ℝ) * ((m : ℝ) + 1) *
        Real.log (((m : ℝ) + 1) / (2 * (m : ℝ)) *
          Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / tau A u)⌋) :=
  OblivEllipsoid.Infeas.OEAThm71.thm71 A u hA ell Lam hcert hinf
