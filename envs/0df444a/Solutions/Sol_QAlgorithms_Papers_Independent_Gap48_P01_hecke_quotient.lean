-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.hecke_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:08:19.535473+00:00
-- url     : https://prove2.me/submissions/a1b68e01-0a70-4786-9765-fe65ce0627ac

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Gap48.P01

section g73i
variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

theorem g73i_amm {A : Type*} [Ring A] [Algebra R A] (a b : R) (z : A) :
    algebraMap R A a * (algebraMap R A b * z) = algebraMap R A (a * b) * z := by
  rw [← mul_assoc, ← map_mul]

theorem g73i_qq : (P.q : R) * (↑P.q⁻¹ : R) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

abbrev g73i_hk := RingQuot.mkAlgHom R (NonsplitHeckeRel P n)

def g73i_fwdLetter : CyclotomicLetter n → NonsplitHecke P n
  | .x i false => algebraMap R _ (↑P.q⁻¹ : R) * g73i_hk P n (FreeAlgebra.ι R (.x i false))
  | .x i true => algebraMap R _ (P.q : R) * g73i_hk P n (FreeAlgebra.ι R (.x i true))
  | .e _ => 0
  | .y j b => g73i_hk P n (FreeAlgebra.ι R (.y j b))

def g73i_fwdFree : FreeAlgebra R (CyclotomicLetter n) →ₐ[R] NonsplitHecke P n :=
  FreeAlgebra.lift R (g73i_fwdLetter P n)

theorem g73i_fwd_X (i : ℕ) : g73i_fwdFree P n (nonsplitFreeX R n i false) =
    algebraMap R _ (↑P.q⁻¹ : R) * g73i_hk P n (nonsplitFreeX R n i false) := by
  unfold nonsplitFreeX; split_ifs <;> simp [g73i_fwdFree, g73i_fwdLetter]

theorem g73i_fwd_Xi (i : ℕ) : g73i_fwdFree P n (nonsplitFreeX R n i true) =
    algebraMap R _ (P.q : R) * g73i_hk P n (nonsplitFreeX R n i true) := by
  unfold nonsplitFreeX; split_ifs <;> simp [g73i_fwdFree, g73i_fwdLetter]

theorem g73i_fwd_E (i : ℕ) : g73i_fwdFree P n (nonsplitFreeE R n i) = 0 := by
  unfold nonsplitFreeE; split_ifs <;> simp [g73i_fwdFree, g73i_fwdLetter]

theorem g73i_fwd_Y (b : Bool) : g73i_fwdFree P n (nonsplitFreeY R n b) =
    g73i_hk P n (nonsplitFreeY R n b) := by
  unfold nonsplitFreeY; split_ifs <;> simp [g73i_fwdFree, g73i_fwdLetter]

theorem g73i_fwd_rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    g73i_fwdFree P n a = g73i_fwdFree P n b := by
  have hqq := g73i_qq P
  cases h with
  | invL i hi =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.invL (P := P) (n := n) i hi)
    simp only [map_mul, map_one] at h1
    simp only [map_mul, map_one, g73i_fwd_X, g73i_fwd_Xi, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]; simp only [hqq, mul_comm (↑P.q⁻¹ : R), one_smul]
  | invR i hi =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.invR (P := P) (n := n) i hi)
    simp only [map_mul, map_one] at h1
    simp only [map_mul, map_one, g73i_fwd_X, g73i_fwd_Xi, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]; simp only [hqq, mul_comm (↑P.q⁻¹ : R), one_smul]
  | yInvL hn =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.yInvL (P := P) (n := n) hn)
    simp only [map_mul, map_one] at h1
    simp only [map_mul, map_one, g73i_fwd_Y]; exact h1
  | yInvR hn =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.yInvR (P := P) (n := n) hn)
    simp only [map_mul, map_one] at h1
    simp only [map_mul, map_one, g73i_fwd_Y]; exact h1
  | skein i hi =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.invR (P := P) (n := n) i hi)
    have h2 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.quadratic (P := P) (n := n) i hi)
    rw [map_pow, map_add, map_mul, AlgHom.commutes, AlgHom.commutes] at h2
    simp only [map_mul, map_one] at h1
    have h3 : g73i_hk P n (nonsplitFreeX R n i false) = algebraMap R _ ((P.q : R)^2 - 1) +
        algebraMap R _ ((P.q : R)^2) * g73i_hk P n (nonsplitFreeX R n i true) := by
      have : g73i_hk P n (nonsplitFreeX R n i true) * g73i_hk P n (nonsplitFreeX R n i false) ^ 2
          = g73i_hk P n (nonsplitFreeX R n i false) := by rw [pow_two, ← mul_assoc, h1, one_mul]
      rw [h2, mul_add, Algebra.left_comm, h1, mul_one, ← Algebra.commutes] at this
      exact this.symm
    simp only [map_mul, map_sub, map_one, g73i_fwd_X, g73i_fwd_Xi, g73i_fwd_E, sub_zero, mul_one,
      AlgHom.commutes]
    rw [h3, mul_add, g73i_amm, ← map_mul, skeinDelta]
    have e1 : (↑P.q⁻¹ : R) * ((P.q : R)^2 - 1) = (P.q : R) - ↑P.q⁻¹ := by
      linear_combination (P.q : R) * hqq
    have e2 : (↑P.q⁻¹ : R) * (P.q : R)^2 = (P.q : R) := by linear_combination (P.q : R) * hqq
    rw [e1, e2, add_sub_cancel_right]
  | xFar i j hi hj hd =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.far (P := P) (n := n) i j hi hj hd)
    simp only [map_mul] at h1
    simp only [map_mul, g73i_fwd_X, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]
  | braid i hi =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.braid (P := P) (n := n) i hi)
    simp only [map_mul] at h1
    simp only [map_mul, g73i_fwd_X, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_assoc] at h1
    rw [h1]
  | cyclotomic hn =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.cyclotomic (P := P) (n := n) hn)
    simp only [map_mul, map_pow, map_sum, AlgHom.commutes] at h1
    simp only [map_mul, map_pow, map_sum, AlgHom.commutes, g73i_fwd_Y]
    exact h1
  | affine hn =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.affine (P := P) (n := n) hn)
    simp only [map_mul] at h1
    simp only [map_mul, g73i_fwd_X, g73i_fwd_Y, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_assoc] at h1
    rw [h1]
  | yx i hi =>
    have h1 := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.yFar (P := P) (n := n) i hi)
    simp only [map_mul] at h1
    simp only [map_mul, g73i_fwd_X, g73i_fwd_Y, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]
  | _ =>
    simp only [map_mul, map_pow, map_sub, map_one, g73i_fwd_X, g73i_fwd_Xi, g73i_fwd_E,
      g73i_fwd_Y, AlgHom.commutes, mul_zero, zero_mul, pow_two]


abbrev g73i_qm := RingQuot.mkAlgHom R (fun a b : NonsplitBMW P n => a - b ∈ eIdeal P n)

def g73i_fwdB : NonsplitBMW P n →ₐ[R] NonsplitHecke P n :=
  RingQuot.liftAlgHom R ⟨g73i_fwdFree P n, fun _ _ h => g73i_fwd_rel P n h⟩

theorem g73i_fwdB_mk (x : FreeAlgebra R (CyclotomicLetter n)) :
    g73i_fwdB P n (presentationMap P n x) = g73i_fwdFree P n x := by
  unfold g73i_fwdB presentationMap; rw [RingQuot.liftAlgHom_mkAlgHom_apply]

theorem g73i_span_mul {A : Type*} [Ring A] [Algebra R A] (S : Set A)
    (hS : ∀ z ∈ S, ∀ a b : A, a * z * b ∈ S) (z : A) (hz : z ∈ Submodule.span R S) (a b : A) :
    a * z * b ∈ Submodule.span R S := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hS z hz a b)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem g73i_eIdeal_mul (z : NonsplitBMW P n) (hz : z ∈ eIdeal P n) (a b : NonsplitBMW P n) :
    a * z * b ∈ eIdeal P n := by
  apply g73i_span_mul (R := R) _ _ z hz a b
  rintro _ ⟨i, h1, h2, a', b', rfl⟩ a b
  exact ⟨i, h1, h2, a * a', b' * b, by simp only [mul_assoc]⟩

theorem g73i_E_mem (i : ℕ) : E P n i ∈ eIdeal P n := by
  by_cases hi : 1 ≤ i ∧ i < n
  · exact Submodule.subset_span ⟨i, hi.1, hi.2, 1, 1, by simp⟩
  · unfold E nonsplitFreeE; rw [dif_neg hi, map_zero]; exact zero_mem _

theorem g73i_fwdB_eIdeal (z : NonsplitBMW P n) (hz : z ∈ eIdeal P n) : g73i_fwdB P n z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, -, -, a, b, rfl⟩ := hz
    have : g73i_fwdB P n (E P n i) = 0 := by unfold E; rw [g73i_fwdB_mk, g73i_fwd_E]
    rw [map_mul, map_mul, this, mul_zero, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

def g73i_fwdQ : HeckeQuotient P n →ₐ[R] NonsplitHecke P n :=
  RingQuot.liftAlgHom R ⟨g73i_fwdB P n, fun a b h => by
    rw [← sub_eq_zero, ← map_sub]; exact g73i_fwdB_eIdeal P n _ h⟩

theorem g73i_fwdQ_mk (x : NonsplitBMW P n) : g73i_fwdQ P n (g73i_qm P n x) = g73i_fwdB P n x := by
  unfold g73i_fwdQ; rw [RingQuot.liftAlgHom_mkAlgHom_apply]

theorem g73i_qm_eIdeal (z : NonsplitBMW P n) (hz : z ∈ eIdeal P n) : g73i_qm P n z = 0 := by
  rw [← map_zero (g73i_qm P n)]; exact RingQuot.mkAlgHom_rel R (by simpa using hz)

def g73i_revLetter : CyclotomicLetter n → HeckeQuotient P n
  | .x i false => algebraMap R _ (P.q : R) *
      g73i_qm P n (presentationMap P n (FreeAlgebra.ι R (.x i false)))
  | .x i true => algebraMap R _ (↑P.q⁻¹ : R) *
      g73i_qm P n (presentationMap P n (FreeAlgebra.ι R (.x i true)))
  | .e _ => 0
  | .y j b => g73i_qm P n (presentationMap P n (FreeAlgebra.ι R (.y j b)))

def g73i_revFree : FreeAlgebra R (CyclotomicLetter n) →ₐ[R] HeckeQuotient P n :=
  FreeAlgebra.lift R (g73i_revLetter P n)

theorem g73i_rev_X (i : ℕ) : g73i_revFree P n (nonsplitFreeX R n i false) =
    algebraMap R _ (P.q : R) * g73i_qm P n (X P n i false) := by
  unfold X nonsplitFreeX; split_ifs <;> simp [g73i_revFree, g73i_revLetter]

theorem g73i_rev_Xi (i : ℕ) : g73i_revFree P n (nonsplitFreeX R n i true) =
    algebraMap R _ (↑P.q⁻¹ : R) * g73i_qm P n (X P n i true) := by
  unfold X nonsplitFreeX; split_ifs <;> simp [g73i_revFree, g73i_revLetter]

theorem g73i_rev_E (i : ℕ) : g73i_revFree P n (nonsplitFreeE R n i) = 0 := by
  unfold nonsplitFreeE; split_ifs <;> simp [g73i_revFree, g73i_revLetter]

theorem g73i_rev_Y (b : Bool) : g73i_revFree P n (nonsplitFreeY R n b) =
    g73i_qm P n (Y P n b) := by
  unfold Y nonsplitFreeY; split_ifs <;> simp [g73i_revFree, g73i_revLetter]

theorem g73i_bmw {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    g73i_qm P n (presentationMap P n a) = g73i_qm P n (presentationMap P n b) := by
  unfold presentationMap; rw [RingQuot.mkAlgHom_rel R h]

theorem g73i_pmX (i : ℕ) (b : Bool) : presentationMap P n (nonsplitFreeX R n i b) = X P n i b := rfl
theorem g73i_pmE (i : ℕ) : presentationMap P n (nonsplitFreeE R n i) = E P n i := rfl
theorem g73i_pmY (b : Bool) : presentationMap P n (nonsplitFreeY R n b) = Y P n b := rfl

theorem g73i_rev_rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitHeckeRel P n a b) :
    g73i_revFree P n a = g73i_revFree P n b := by
  have hqq := g73i_qq P
  cases h with
  | invL i hi =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.invL (P := P) (n := n) i hi)
    simp only [map_mul, map_one, g73i_pmX] at h1
    simp only [map_mul, map_one, g73i_rev_X, g73i_rev_Xi, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]; simp only [hqq, mul_comm (↑P.q⁻¹ : R), one_smul]
  | invR i hi =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.invR (P := P) (n := n) i hi)
    simp only [map_mul, map_one, g73i_pmX] at h1
    simp only [map_mul, map_one, g73i_rev_X, g73i_rev_Xi, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]; simp only [hqq, mul_comm (↑P.q⁻¹ : R), one_smul]
  | yInvL hn =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.yInvL (P := P) (n := n) hn)
    simp only [map_mul, map_one, g73i_pmY] at h1
    simp only [map_mul, map_one, g73i_rev_Y]; exact h1
  | yInvR hn =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.yInvR (P := P) (n := n) hn)
    simp only [map_mul, map_one, g73i_pmY] at h1
    simp only [map_mul, map_one, g73i_rev_Y]; exact h1
  | braid i hi =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.braid (P := P) (n := n) i hi)
    simp only [map_mul, g73i_pmX] at h1
    simp only [map_mul, g73i_rev_X, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_assoc] at h1
    rw [h1]
  | far i j hi hj hd =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.xFar (P := P) (n := n) i j hi hj hd)
    simp only [map_mul, g73i_pmX] at h1
    simp only [map_mul, g73i_rev_X, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]
  | affine hn =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.affine (P := P) (n := n) hn)
    simp only [map_mul, g73i_pmX, g73i_pmY] at h1
    simp only [map_mul, g73i_rev_X, g73i_rev_Y, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_assoc] at h1
    rw [h1]
  | yFar i hi =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.yx (P := P) (n := n) i hi)
    simp only [map_mul, g73i_pmX, g73i_pmY] at h1
    simp only [map_mul, g73i_rev_X, g73i_rev_Y, mul_assoc]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]
  | cyclotomic hn =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.cyclotomic (P := P) (n := n) hn)
    simp only [map_mul, map_pow, map_sum, AlgHom.commutes, g73i_pmY] at h1
    simp only [map_mul, map_pow, map_sum, AlgHom.commutes, g73i_rev_Y]
    exact h1
  | quadratic i hi =>
    have h1 := g73i_bmw P n (NonsplitBMWRel.invL (P := P) (n := n) i hi)
    have h2 := g73i_bmw P n (NonsplitBMWRel.skein (P := P) (n := n) i hi)
    have h3 := g73i_qm_eIdeal P n _ (g73i_E_mem P n i)
    simp only [map_mul, map_one, g73i_pmX] at h1
    simp only [map_mul, map_sub, map_one, AlgHom.commutes, g73i_pmX, g73i_pmE] at h2
    have h2' : g73i_qm P n (X P n i false) - g73i_qm P n (X P n i true) =
        algebraMap R (HeckeQuotient P n) (skeinDelta P) := by
      rw [h2]; erw [h3, sub_zero, mul_one]
    have h4 : g73i_qm P n (X P n i false) ^ 2 =
        1 + algebraMap R (HeckeQuotient P n) (skeinDelta P) * g73i_qm P n (X P n i false) := by
      have : g73i_qm P n (X P n i false) = g73i_qm P n (X P n i true) +
          algebraMap R (HeckeQuotient P n) (skeinDelta P) := by rw [← h2']; abel
      conv_lhs => rw [pow_two]; arg 2; rw [this]
      rw [mul_add, h1, ← Algebra.commutes]
    simp only [map_pow, map_add, map_mul, AlgHom.commutes, g73i_rev_X]
    rw [pow_two, mul_assoc, Algebra.left_comm (g73i_qm P n (X P n i false)), ← mul_assoc,
      ← map_mul, ← pow_two (g73i_qm P n (X P n i false)), h4]
    simp only [mul_add, mul_one, ← mul_assoc, ← map_mul, ← map_pow]
    rw [add_comm, skeinDelta]
    congr 1
    · congr 2; linear_combination (-(P.q : R)) * hqq
    · congr 1; ring
  | killE i hi =>
    simp only [g73i_rev_E, map_zero]

end g73i

section g73i3
variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def g73i_revQ : NonsplitHecke P n →ₐ[R] HeckeQuotient P n :=
  RingQuot.liftAlgHom R ⟨g73i_revFree P n, fun _ _ h => g73i_rev_rel P n h⟩

theorem g73i_revQ_mk (x : FreeAlgebra R (CyclotomicLetter n)) :
    g73i_revQ P n (g73i_hk P n x) = g73i_revFree P n x := by
  unfold g73i_revQ; rw [RingQuot.liftAlgHom_mkAlgHom_apply]

theorem g73i_hk_e (i : {i : ℕ // 1 ≤ i ∧ i < n}) :
    g73i_hk P n (FreeAlgebra.ι R (CyclotomicLetter.e i)) = 0 := by
  have h := RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.killE (P := P) (n := n) i.1 i.2)
  rw [map_zero] at h
  unfold nonsplitFreeE at h; rw [dif_pos i.2] at h
  exact h

theorem g73i_qm_e (i : {i : ℕ // 1 ≤ i ∧ i < n}) :
    g73i_qm P n (presentationMap P n (FreeAlgebra.ι R (CyclotomicLetter.e i))) = 0 := by
  have h := g73i_qm_eIdeal P n _ (g73i_E_mem P n i.1)
  unfold E nonsplitFreeE at h; rw [dif_pos i.2] at h
  exact h

def g73i_iso : HeckeQuotient P n ≃ₐ[R] NonsplitHecke P n := by
  have hqq := g73i_qq P
  refine AlgEquiv.ofAlgHom (g73i_fwdQ P n) (g73i_revQ P n) ?_ ?_
  · apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext x
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      FreeAlgebra.ι_comp_lift, AlgHom.toLinearMap_apply, AlgHom.coe_comp, AlgHom.id_comp]
    rw [g73i_revQ_mk]
    cases x with
    | x i b =>
      cases b <;> simp only [g73i_revFree, g73i_revLetter, FreeAlgebra.lift_ι_apply] <;>
        erw [map_mul, AlgHom.commutes, g73i_fwdQ_mk, g73i_fwdB_mk] <;>
        simp [g73i_fwdFree, g73i_fwdLetter, ← mul_assoc, ← map_mul, hqq, mul_comm (↑P.q⁻¹ : R)]
    | e i => simp [g73i_revFree, g73i_revLetter, g73i_hk_e]
    | y j b => simp [g73i_revFree, g73i_revLetter, g73i_fwdQ_mk, g73i_fwdB_mk, g73i_fwdFree,
        g73i_fwdLetter]
  · apply RingQuot.ringQuot_ext'
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext x
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      FreeAlgebra.ι_comp_lift, AlgHom.toLinearMap_apply, AlgHom.coe_comp, AlgHom.id_comp]
    have hpm : ∀ z, RingQuot.mkAlgHom R (NonsplitBMWRel P n) z = presentationMap P n z :=
      fun _ => rfl
    rw [hpm, g73i_fwdQ_mk, g73i_fwdB_mk]
    cases x with
    | x i b =>
      cases b <;> simp only [g73i_fwdFree, g73i_fwdLetter, FreeAlgebra.lift_ι_apply] <;>
        erw [map_mul, AlgHom.commutes, g73i_revQ_mk] <;>
        simp [g73i_revFree, g73i_revLetter, ← mul_assoc, ← map_mul, hqq, mul_comm (↑P.q⁻¹ : R)]
    | e i => simp [g73i_fwdFree, g73i_fwdLetter, g73i_qm_e]
    | y j b => simp [g73i_revQ_mk, g73i_revFree, g73i_revLetter, g73i_fwdFree, g73i_fwdLetter]

theorem g73i_iso_mk (x : NonsplitBMW P n) :
    g73i_iso P n (g73i_qm P n x) = g73i_fwdB P n x := by
  unfold g73i_iso; exact g73i_fwdQ_mk P n x

theorem g73i_rel_sub {a b : NonsplitBMW P n}
    (h : Relation.EqvGen (RingQuot.Rel (fun a b : NonsplitBMW P n => a - b ∈ eIdeal P n)) a b) :
    a - b ∈ eIdeal P n := by
  induction h with
  | rel x y hxy =>
    induction hxy with
    | of h => exact h
    | add_left _ ih => simpa using ih
    | mul_left _ ih =>
      rw [← sub_mul]; simpa using g73i_eIdeal_mul P n _ ih 1 _
    | mul_right _ ih =>
      rw [← mul_sub]; simpa using g73i_eIdeal_mul P n _ ih _ 1
  | refl => simp
  | symm x y _ ih => rw [← neg_sub]; exact neg_mem ih
  | trans x y z _ _ ih1 ih2 => rw [← sub_add_sub_cancel]; exact add_mem ih1 ih2

theorem g73i_qm_zero (a : NonsplitBMW P n) (h : g73i_qm P n a = 0) : a ∈ eIdeal P n := by
  have e : ∀ x, g73i_qm P n x = ⟨Quot.mk _ x⟩ := fun x => by
    simp only [g73i_qm, RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def]; rfl
  have h' : (⟨Quot.mk _ a⟩ : HeckeQuotient P n) = ⟨Quot.mk _ 0⟩ := by
    rw [← e, ← e, h, map_zero]
  have h'' := Quot.eqvGen_exact (RingQuot.mk.inj h')
  simpa using g73i_rel_sub P n h''

theorem g73i_J_mul (j : ℕ) (z : NonsplitBMW P n)
    (hz : z ∈ Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b})
    (a b : NonsplitBMW P n) :
    a * z * b ∈ Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b} := by
  apply g73i_span_mul (R := R) _ _ z hz a b
  rintro _ ⟨a', b', rfl⟩ a b
  exact ⟨a * a', b' * b, by simp only [mul_assoc]⟩

theorem g73i_J_le (i j : ℕ) (h : E P n i ∈ Submodule.span R
      {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b}) :
    Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n i * b} ≤
      Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b} := by
  rw [Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  exact g73i_J_mul P n j _ h a b

theorem g73i_xinv (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i true * X P n i false = 1 := by
  have h := RingQuot.mkAlgHom_rel R (NonsplitBMWRel.invR (P := P) (n := n) i hi)
  simpa only [X, presentationMap, map_mul, map_one] using h

theorem g73i_J_eq (i : ℕ) (hi : 1 ≤ i) (hin : i + 1 < n) :
    Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n i * b} =
      Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n (i+1) * b} := by
  have hx1 := g73i_xinv P n i ⟨hi, by omega⟩
  have hx2 := g73i_xinv P n (i+1) ⟨by omega, hin⟩
  apply le_antisymm
  · apply g73i_J_le
    have h := RingQuot.mkAlgHom_rel R (NonsplitBMWRel.nearL (P := P) (n := n) i (i+1)
      ⟨hi, by omega⟩ ⟨by omega, hin⟩ (Or.inl rfl))
    have h' : X P n i false * X P n (i+1) false * E P n i = E P n (i+1) * E P n i := by
      simpa only [X, E, presentationMap, map_mul] using h
    refine Submodule.subset_span ⟨X P n (i+1) true * X P n i true, E P n i, ?_⟩
    calc E P n i = X P n (i+1) true * (X P n i true * X P n i false) * X P n (i+1) false *
          E P n i := by rw [hx1, mul_one, hx2, one_mul]
      _ = X P n (i+1) true * X P n i true * (X P n i false * X P n (i+1) false * E P n i) := by
          simp only [mul_assoc]
      _ = _ := by rw [h']; simp only [mul_assoc]
  · apply g73i_J_le
    have h := RingQuot.mkAlgHom_rel R (NonsplitBMWRel.nearL (P := P) (n := n) (i+1) i
      ⟨by omega, hin⟩ ⟨hi, by omega⟩ (Or.inr rfl))
    have h' : X P n (i+1) false * X P n i false * E P n (i+1) = E P n i * E P n (i+1) := by
      simpa only [X, E, presentationMap, map_mul] using h
    refine Submodule.subset_span ⟨X P n i true * X P n (i+1) true, E P n (i+1), ?_⟩
    calc E P n (i+1) = X P n i true * (X P n (i+1) true * X P n (i+1) false) * X P n i false *
          E P n (i+1) := by rw [hx2, mul_one, hx1, one_mul]
      _ = X P n i true * X P n (i+1) true * (X P n (i+1) false * X P n i false * E P n (i+1)) := by
          simp only [mul_assoc]
      _ = _ := by rw [h']; simp only [mul_assoc]

theorem g73i_J_one (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n i * b} =
      Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n 1 * b} := by
  induction i with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · rw [← g73i_J_eq P n m hm hin, ih hm (by omega)]

end g73i3

/-- Unnumbered canonical Hecke quotient, PDF pp.10--11,20.
The quotient equivalence is characterized on every source generator:
Y maps to T_0, X_i to q inverse times T_i, and e_i to zero.
The composite with the computed quotient map is surjective with exactly the
all-e ideal as kernel, and is bijective at n=0,1. Every valid single e_j
also generates that ideal. No admissibility is required. Definition 3.1's
printed quadratic range 1,...,n-2 is corrected to 1,...,n-1, as forced by
the p.11 quotient calculation; round 1 independently accepts this correction. -/
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    let quotientMap := RingQuot.mkAlgHom R
      (fun a b : NonsplitBMW P n => a-b ∈ eIdeal P n)
    let heckeMap := RingQuot.mkAlgHom R (NonsplitHeckeRel P n)
    (∃ iso : HeckeQuotient P n ≃ₐ[R] NonsplitHecke P n,
      (0 < n → iso (quotientMap (Y P n false)) = heckeMap (nonsplitFreeY R n false)) ∧
      (∀ i, 1 ≤ i → i < n →
        iso (quotientMap (X P n i false)) =
          algebraMap R _ (↑P.q⁻¹ : R) * heckeMap (nonsplitFreeX R n i false)) ∧
      (∀ i, 1 ≤ i → i < n → iso (quotientMap (E P n i)) = 0) ∧
      Function.Surjective (fun a => iso (quotientMap a)) ∧
      (∀ a, iso (quotientMap a) = 0 ↔ a ∈ eIdeal P n) ∧
      (n ≤ 1 → Function.Bijective (fun a => iso (quotientMap a)))) ∧
    (∀ j, 1 ≤ j → j < n → eIdeal P n =
      Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b}) := by
  intro quotientMap heckeMap
  have hker : ∀ a, g73i_iso P n (quotientMap a) = 0 ↔ a ∈ eIdeal P n := by
    intro a
    rw [map_eq_zero_iff _ (g73i_iso P n).injective]
    exact ⟨g73i_qm_zero P n a, g73i_qm_eIdeal P n a⟩
  refine ⟨⟨g73i_iso P n, ?_, ?_, ?_, ?_, hker, ?_⟩, ?_⟩
  · intro _
    show g73i_iso P n (g73i_qm P n (Y P n false)) = _
    rw [g73i_iso_mk]; unfold Y; rw [g73i_fwdB_mk, g73i_fwd_Y]
  · intro i _ _
    show g73i_iso P n (g73i_qm P n (X P n i false)) = _
    rw [g73i_iso_mk]; unfold X; rw [g73i_fwdB_mk, g73i_fwd_X]
  · intro i _ _
    show g73i_iso P n (g73i_qm P n (E P n i)) = _
    rw [g73i_iso_mk]; unfold E; rw [g73i_fwdB_mk, g73i_fwd_E]
  · exact (g73i_iso P n).surjective.comp (RingQuot.mkAlgHom_surjective R _)
  · intro hn
    refine ⟨fun a b hab => ?_, (g73i_iso P n).surjective.comp (RingQuot.mkAlgHom_surjective R _)⟩
    have h1 : g73i_iso P n (quotientMap (a - b)) = 0 := by
      simp only [map_sub]; exact sub_eq_zero.mpr hab
    have h2 := (hker _).mp h1
    have h3 : eIdeal P n = ⊥ := by
      unfold eIdeal
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, h1, h2, -⟩; omega
    rw [h3, Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  · intro j hj hjn
    apply le_antisymm
    · unfold eIdeal; rw [Submodule.span_le]
      rintro _ ⟨i, hi, hin, a, b, rfl⟩
      have : Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n i * b} =
          Submodule.span R {z | ∃ a b : NonsplitBMW P n, z = a * E P n j * b} := by
        rw [g73i_J_one P n i hi hin, g73i_J_one P n j hj hjn]
      rw [SetLike.mem_coe, ← this]
      exact Submodule.subset_span ⟨a, b, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨a, b, rfl⟩
      exact Submodule.subset_span ⟨j, hj, hjn, a, b, rfl⟩

end
