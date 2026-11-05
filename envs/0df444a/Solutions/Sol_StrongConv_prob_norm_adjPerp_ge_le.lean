-- Prove2me | solution 1 for StrongConv.prob_norm_adjPerp_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:12:09.530979+00:00
-- url     : https://prove2.me/submissions/b9059d8f-2db0-49dd-9ce1-b64556fa3187

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_prob_norm_eval_sModel_ge_le
import Theorems.Thm_StrongConv_norm_adjFree

open Polynomial Filter Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace StrongConv

def T34_P (d : ℕ) : NCPoly 1 d :=
  ∑ l : Fin d ⊕ Fin d, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)

lemma T34_tensorOp_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (T : H →L[ℂ] H) : tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x i
  simp [tensorOp]

lemma T34_tensorOp_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  ext x i
  simp [tensorOp, add_smul, Finset.sum_add_distrib]

lemma T34_sum_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) (s : Finset (Fin d ⊕ Fin d)) :
    (∑ l ∈ s, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)).sum
      (fun w A => tensorOp A (wordOp u w)) =
      ∑ l ∈ s, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      Finsupp.sum_add_index' (fun w => T34_tensorOp_zero _) (fun w A B => T34_tensorOp_add A B _), ih,
      Finsupp.sum_single_index (T34_tensorOp_zero _)]
    simp [wordOp]

lemma T34_eval_P {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T34_P d).eval u = ∑ l : Fin d ⊕ Fin d, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) :=
  T34_sum_single d u Finset.univ

/-- the identification `PiLp 2 (Fin 1 → H) ≃ H` -/
def T34_E (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    PiLp 2 (fun _ : Fin 1 => H) ≃ₗᵢ[ℂ] H where
  toFun x := x 0
  invFun y := WithLp.toLp 2 (fun _ => y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    ext i
    have : i = 0 := Subsingleton.elim _ _
    subst this; rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x 0‖ = ‖x‖
    rw [PiLp.norm_eq_of_L2]
    simp

lemma T34_tensorOp_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) T = (T34_E H).symm.conjStarAlgEquiv T := by
  ext x i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [tensorOp, T34_E]
  rfl

lemma T34_eval_P' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T34_P d).eval u = (T34_E H).symm.conjStarAlgEquiv (∑ i, (u i + star (u i))) := by
  rw [T34_eval_P]
  simp only [T34_tensorOp_one, ← map_sum, Fintype.sum_sum_type, letterOp, Finset.sum_add_distrib]


/-! ## Part A: facts about `P` -/

lemma T34_P_apply (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    T34_P d w = if w.length = 1 then 1 else 0 := by
  classical
  unfold T34_P
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hw : w.length = 1
  · obtain ⟨a, ha⟩ : ∃ a, w = FreeMonoid.of a := by
      have : w.toList.length = 1 := hw
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp this
      exact ⟨a, by apply FreeMonoid.toList.injective; simpa using ha⟩
    subst ha
    rw [if_pos hw, Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)]
    · simp
    · rw [if_neg]
      intro h
      exact hb (FreeMonoid.of_injective h)
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg]
    rintro rfl
    exact hw (by simp)

lemma T34_wordStar_length (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    (NCPoly.wordStar w).length = w.length := by
  simp [NCPoly.wordStar, FreeMonoid.length]

lemma T34_P_selfAdjoint (d : ℕ) : (T34_P d).IsSelfAdjoint := by
  intro w
  rw [T34_P_apply, T34_P_apply, T34_wordStar_length]
  split_ifs <;> simp

lemma T34_P_degree (d : ℕ) : (T34_P d).degree ≤ 1 := by
  unfold NCPoly.degree
  apply Finset.sup_le
  intro w hw
  rw [Finsupp.mem_support_iff, T34_P_apply] at hw
  by_contra hc
  exact hw (if_neg (by omega))

lemma T34_norm_unitary_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) with hs | hs
  · rw [Subsingleton.elim (Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)) 0]
    simp
  · have hU := Unitary.mem_iff.mp U.2
    have hmem : Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ) ∈
        unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [Unitary.mem_iff]
      constructor
      · rw [← map_star, ← map_mul, hU.1, map_one]
      · rw [← map_star, ← map_mul, hU.2, map_one]
    exact (CStarRing.norm_of_mem_unitary hmem).le

lemma T34_norm_eval_le (d : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖(T34_P d).eval u‖ ≤ 2 * d := by
  rw [T34_eval_P', StarAlgEquiv.norm_map]
  calc ‖∑ i, (u i + star (u i))‖ ≤ ∑ i, ‖u i + star (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖u i + star (u i)‖ ≤ ‖u i‖ + ‖star (u i)‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_star]; linarith [hu i]
    _ = 2 * d := by simp [mul_comm]

lemma T34_fullNorm (d : ℕ) : (T34_P d).fullNorm = 2 * d := by
  unfold NCPoly.fullNorm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨1, fun _ => 1, ?_⟩
    rw [T34_eval_P', StarAlgEquiv.norm_map]
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ)
        (((1 : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ)) =
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) := by
      simp
    simp only [h1, star_one]
    rw [← two_smul ℂ (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, norm_smul, norm_one]
    simp
    ring
  · rintro x ⟨n, U, rfl⟩
    exact T34_norm_eval_le d _ fun i => T34_norm_unitary_le (U i)



lemma T34_norm_eval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    ‖(T34_P d).eval u‖ = ‖∑ i, (u i + star (u i))‖ := by
  rw [T34_eval_P', StarAlgEquiv.norm_map]

lemma T34_norm_sLimit (d : ℕ) : ‖(T34_P d).eval (sLimit d)‖ = ‖adjFree d‖ :=
  T34_norm_eval d (sLimit d)

lemma T34_norm_sModel (d N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖(T34_P d).eval (sModel σ)‖ = ‖adjPerp σ‖ :=
  T34_norm_eval d (sModel σ)

theorem prob_norm_adjPerp_ge_le_dev :
    ∃ C : ℝ, ∀ d N : ℕ, 2 ≤ d → 1 ≤ N → ∀ ε : ℝ, 0 < ε →
      ε < 2 * d - 2 * Real.sqrt (2 * d - 1) →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖) ≤
        C * (1 / N) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε) := by
  obtain ⟨C, hC⟩ := prob_norm_eval_sModel_ge_le
  refine ⟨max (C * 2 ^ 8) 0, fun d N hd hN ε hε hεd => ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hF := norm_adjFree d (by omega)
  have hfn := T34_fullNorm d
  have hε' : ε < (T34_P d).fullNorm - ‖(T34_P d).eval (sLimit d)‖ := by
    rw [hfn, T34_norm_sLimit, hF]; exact hεd
  have h := hC 1 d 1 hd (T34_P d) (T34_P_selfAdjoint d) (by simpa using T34_P_degree d) ε hε hε' N
  rw [T34_norm_sLimit, hF] at h
  simp only [T34_norm_sModel] at h
  rw [hfn] at h
  have hdpos : (0 : ℝ) < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hs : Real.sqrt (2 * d - 1) ≤ d := by
    apply Real.sqrt_le_iff.mpr; constructor <;> nlinarith
  have hlog : 0 ≤ Real.log (2 * Real.exp 1 * d / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    have : ε < 2 * d := by linarith [Real.sqrt_nonneg (2 * (d:ℝ) - 1)]
    have he : (1:ℝ) ≤ Real.exp 1 := by simpa using Real.add_one_le_exp (1:ℝ)
    nlinarith
  have hlog' : Real.log (Real.exp 1 * (2 * d) / ε) = Real.log (2 * Real.exp 1 * d / ε) := by
    congr 1; ring
  have hnn : 0 ≤ (1 / (N:ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε) := by
    positivity
  refine h.trans ?_
  rw [hlog']
  have e : (((1:ℕ):ℝ) / N) * (2 * d * ((1:ℕ):ℝ) * Real.log d / ε) ^ 8 *
      Real.log (2 * Real.exp 1 * d / ε) =
      2 ^ 8 * ((1 / (N:ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) := by
    push_cast; field_simp
  have e2 : max (C * 2 ^ 8) 0 * (1 / (N:ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)
      = max (C * 2 ^ 8) 0 * ((1 / (N:ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) := by ring
  rw [e2]
  calc _ = C * (((1:ℕ):ℝ) / N * (2 * d * ((1:ℕ):ℝ) * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) := by ring
    _ = C * 2 ^ 8 * ((1 / (N:ℝ)) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε)) := by rw [e]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hnn

end StrongConv

theorem solution : type_of% @StrongConv.prob_norm_adjPerp_ge_le_dev := @StrongConv.prob_norm_adjPerp_ge_le_dev
