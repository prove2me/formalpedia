-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.sharing_convex_and_mixing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:40:21.328193+00:00
-- url     : https://prove2.me/submissions/776dba14-0e1e-4564-9691-229547e80a46

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

end QAlgorithms.Papers.Independent.Extend50.P36

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem s110sc_marg {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (X Y : Op (SharingIndex I J m n)) (a b : ℝ) (i : Fin m) (j : Fin n) :
    sharingMarginal (a • X + b • Y) i j =
      a • sharingMarginal X i j + b • sharingMarginal Y i j := by
  ext u v
  simp only [sharingMarginal, Matrix.add_apply, Matrix.smul_apply, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem s110sc_dens {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ)
    (hX : QAlgorithms.IsDensityMatrix X) (hY : QAlgorithms.IsDensityMatrix Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    QAlgorithms.IsDensityMatrix (a • X + b • Y) := by
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2, ← add_smul, hab, one_smul]

theorem s110sc_count {I : Type*} [Fintype I] {m : ℕ} (i : Fin m) (a : I) :
    (∑ x : Fin m → I, if x i = a then (1 : ℂ) else 0) =
      (Fintype.card I : ℂ) ^ (m - 1) := by
  rw [← Fintype.sum_equiv (Equiv.piSplitAt i (fun _ => I)).symm _ _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp [Equiv.piSplitAt, Fintype.card_pi, Finset.card_univ]

theorem s110sc_fm {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Sharable m n (fullyMixed (I × J)) := by
  refine ⟨fullyMixed (SharingIndex I J m n), ⟨?_, ?_⟩, fun i j => ?_⟩
  · unfold fullyMixed
    refine Matrix.PosSemidef.one.smul ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (by positivity)
  · have : (Fintype.card (SharingIndex I J m n) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [fullyMixed, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    field_simp
  · ext a b
    simp only [sharingMarginal, fullyMixed, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      have h1 : ∀ (x : Fin m → I) (y : Fin n → J), (if x i = a.1 ∧ y j = a.2 then
          (Fintype.card (SharingIndex I J m n) : ℂ)⁻¹ *
            (if (x, y) = (Function.update x i a.1, Function.update y j a.2) then 1 else 0)
          else 0) = (Fintype.card (SharingIndex I J m n) : ℂ)⁻¹ *
            ((if x i = a.1 then 1 else 0) * (if y j = a.2 then 1 else 0)) := by
        intro x y
        by_cases hx : x i = a.1
        · by_cases hy : y j = a.2
          · rw [if_pos ⟨hx, hy⟩, if_pos, if_pos hx, if_pos hy]
            · simp
            · rw [← hx, ← hy]; simp
          · simp [hy]
        · simp [hx]
      simp only [h1, ← Finset.mul_sum, s110sc_count]
      simp only [← Finset.sum_mul, s110sc_count]
      have hI : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hJ : (Fintype.card J : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [SharingIndex, Fintype.card_prod, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [if_pos trivial]
      field_simp
      ring
    · rw [if_neg hab, mul_zero]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      split_ifs with h1 h2
      · exfalso; apply hab
        have hx := congrArg (fun p => p.1 i) h2
        have hy := congrArg (fun p => p.2 j) h2
        simp at hx hy
        exact Prod.ext (h1.1.symm.trans hx) (h1.2.symm.trans hy)
      · simp
      · rfl

theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Convex ℝ {rho : Op (I × J) | Sharable m n rho} ∧
    ArbitrarilySharable (fullyMixed (I × J)) ∧
    (∀ rho : Op (I × J), Sharable m n rho → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Sharable m n (convexStateMixture t rho (fullyMixed (I × J)))) := by
  have hconv : ∀ m n : ℕ, Convex ℝ {rho : Op (I × J) | Sharable m n rho} := by
    intro m n
    rintro r1 ⟨X1, hX1, hm1⟩ r2 ⟨X2, hX2, hm2⟩ a b ha hb hab
    refine ⟨a • X1 + b • X2, s110sc_dens X1 X2 hX1 hX2 a b ha hb hab, fun i j => ?_⟩
    rw [s110sc_marg, hm1, hm2]
  refine ⟨hconv m n, fun m n hm hn => s110sc_fm m n hm hn, ?_⟩
  intro rho hr t ht0 ht1
  have := hconv m n hr (s110sc_fm m n hm hn) (a := t) (b := 1 - t) ht0 (by linarith) (by ring)
  have e : convexStateMixture t rho (fullyMixed (I × J)) = t • rho + (1 - t) • fullyMixed (I × J) := by
    ext a b; simp [convexStateMixture, Complex.real_smul]
  rw [e]; exact this
