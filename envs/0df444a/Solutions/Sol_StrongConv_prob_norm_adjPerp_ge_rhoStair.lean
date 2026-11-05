-- Prove2me | solution 1 for StrongConv.prob_norm_adjPerp_ge_rhoStair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:24:20.149072+00:00
-- url     : https://prove2.me/submissions/c6f322af-bf56-40c4-9e68-a621c78ad201
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_sub_le
import Theorems.Thm_StrongConv_exists_testFunction
import Theorems.Thm_StrongConv_supp_subset_Icc_rhoStair_of_extends_nuAdj
import Theorems.Thm_StrongConv_prob_norm_adjPerp_ge_of_lt_rhoStair

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace StrongConv

section T36_a
open Polynomial Filter Topology


def T36_P (d : ℕ) : NCPoly 1 d :=
  ∑ l : Fin d ⊕ Fin d, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)

lemma T36_tensorOp_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (T : H →L[ℂ] H) : tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x i
  simp [tensorOp]

lemma T36_tensorOp_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  ext x i
  simp [tensorOp, add_smul, Finset.sum_add_distrib]

lemma T36_sum_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) (s : Finset (Fin d ⊕ Fin d)) :
    (∑ l ∈ s, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)).sum
      (fun w A => tensorOp A (wordOp u w)) =
      ∑ l ∈ s, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      Finsupp.sum_add_index' (fun w => T36_tensorOp_zero _) (fun w A B => T36_tensorOp_add A B _), ih,
      Finsupp.sum_single_index (T36_tensorOp_zero _)]
    simp [wordOp]

lemma T36_eval_P {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T36_P d).eval u = ∑ l : Fin d ⊕ Fin d, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) :=
  T36_sum_single d u Finset.univ

/-- the identification `PiLp 2 (Fin 1 → H) ≃ H` -/
def T36_E (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
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

lemma T36_tensorOp_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) T = (T36_E H).symm.conjStarAlgEquiv T := by
  ext x i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [tensorOp, T36_E]
  rfl

lemma T36_eval_P' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T36_P d).eval u = (T36_E H).symm.conjStarAlgEquiv (∑ i, (u i + star (u i))) := by
  rw [T36_eval_P]
  simp only [T36_tensorOp_one, ← map_sum, Fintype.sum_sum_type, letterOp, Finset.sum_add_distrib]

lemma T36_isSelfAdjoint_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) :=
  isSelfAdjoint_sum _ fun i _ => IsSelfAdjoint.add_star_self (u i)

lemma T36_fnCalc_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : ℝ → ℝ) (hh : Continuous h) (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    fnCalc h ((T36_E H).symm.conjStarAlgEquiv a) =
      (T36_E H).symm.conjStarAlgEquiv (fnCalc h a) := by
  have hn : IsStarNormal a := ha.isStarNormal
  unfold fnCalc
  have hc : Continuous (fun z : ℂ => ((h z.re : ℝ) : ℂ)) := by fun_prop
  have hcont : Continuous (T36_E H).symm.conjStarAlgEquiv := by
    have : (fun T : H →L[ℂ] H => (T36_E H).symm.conjStarAlgEquiv T) =
        fun T => ((T36_E H).symm.toContinuousLinearEquiv : _ →L[ℂ] _) ∘L T ∘L
          ((T36_E H).toContinuousLinearEquiv : _ →L[ℂ] _) := rfl
    show Continuous (fun T : H →L[ℂ] H => (T36_E H).symm.conjStarAlgEquiv T)
    rw [this]
    fun_prop
  exact (StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) (T36_E H).symm.conjStarAlgEquiv
      (fun z : ℂ => ((h z.re : ℝ) : ℂ)) a hc.continuousOn hcont hn
      (ha.map _).isStarNormal).symm

lemma T36_trace_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : H →L[ℂ] H) :
    LinearMap.trace ℂ _ (((T36_E H).symm.conjStarAlgEquiv a : PiLp 2 (fun _ : Fin 1 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 1 => H)) : PiLp 2 (fun _ : Fin 1 => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin 1 => H)) =
      LinearMap.trace ℂ _ (a : H →ₗ[ℂ] H) := by
  have := LinearMap.trace_conj' (a : H →ₗ[ℂ] H) (T36_E H).symm.toLinearEquiv
  rw [← this]
  congr 1

theorem T36_trDN_eval (d N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (h : ℝ → ℝ) (hh : Continuous h) :
    trDN 1 N (fnCalc h ((T36_P d).eval (sModel σ))) = trN N (fnCalc h (adjPerp σ)) := by
  rw [T36_eval_P' d (sModel σ)]
  have hsa : IsSelfAdjoint (adjPerp σ) := T36_isSelfAdjoint_sum d (sModel σ)
  have := T36_fnCalc_conj h hh (adjPerp σ) hsa
  have e : (∑ i, (sModel σ i + star (sModel σ i))) = adjPerp σ := rfl
  rw [e, this]
  unfold trDN trN
  rw [T36_trace_conj]
  simp


/-! ## Part A: facts about `P` -/

lemma T36_P_apply (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    T36_P d w = if w.length = 1 then 1 else 0 := by
  classical
  unfold T36_P
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

lemma T36_wordStar_length (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    (NCPoly.wordStar w).length = w.length := by
  simp [NCPoly.wordStar, FreeMonoid.length]

lemma T36_P_selfAdjoint (d : ℕ) : (T36_P d).IsSelfAdjoint := by
  intro w
  rw [T36_P_apply, T36_P_apply, T36_wordStar_length]
  split_ifs <;> simp

lemma T36_P_degree (d : ℕ) : (T36_P d).degree ≤ 1 := by
  unfold NCPoly.degree
  apply Finset.sup_le
  intro w hw
  rw [Finsupp.mem_support_iff, T36_P_apply] at hw
  by_contra hc
  exact hw (if_neg (by omega))

lemma T36_norm_unitary_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
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

lemma T36_norm_eval_le (d : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖(T36_P d).eval u‖ ≤ 2 * d := by
  rw [T36_eval_P', StarAlgEquiv.norm_map]
  calc ‖∑ i, (u i + star (u i))‖ ≤ ∑ i, ‖u i + star (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖u i + star (u i)‖ ≤ ‖u i‖ + ‖star (u i)‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_star]; linarith [hu i]
    _ = 2 * d := by simp [mul_comm]

lemma T36_fullNorm (d : ℕ) : (T36_P d).fullNorm = 2 * d := by
  unfold NCPoly.fullNorm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨1, fun _ => 1, ?_⟩
    rw [T36_eval_P', StarAlgEquiv.norm_map]
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
    exact T36_norm_eval_le d _ fun i => T36_norm_unitary_le (U i)


lemma T36_expTr (d N : ℕ) (h : ℝ → ℝ) (hh : Continuous h) :
    expTr (T36_P d) N h =
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (fnCalc h (adjPerp σ))) := by
  unfold expTr
  congr 1
  funext σ
  exact T36_trDN_eval d N σ h hh

lemma T36_nu_eq (d i : ℕ) (h : ℝ[X]) : nu (T36_P d) i h = nuAdj d i h := by
  unfold nu nuAdj
  have : (fun N : ℕ => expTr (T36_P d) N (fun x => h.eval x)) = fun N : ℕ =>
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (fnCalc (fun x => h.eval x) (adjPerp σ))) := by
    funext N
    exact T36_expTr d N _ h.continuous
  rw [this]


end T36_a

section T36_b
open Filter


lemma T36_s_facts (d : ℕ) (hd : 2 ≤ d) :
    let s := Real.sqrt (2 * (d : ℝ) - 1)
    s * s = 2 * (d : ℝ) - 1 ∧ 1 < s ∧ s ≤ d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 : (0 : ℝ) ≤ 2 * (d : ℝ) - 1 := by linarith
  refine ⟨Real.mul_self_sqrt h0, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, by nlinarith⟩

lemma T36_rho_pos (d m : ℕ) (hd : 2 ≤ d) : 0 < rhoStair d m := by
  obtain ⟨hss, h1, hd2⟩ := T36_s_facts d hd
  unfold rhoStair
  split_ifs with h
  · linarith
  · rw [not_le] at h
    have : (0 : ℝ) < 2 * m - 1 := by linarith
    exact add_pos this (div_pos (by linarith) this)

lemma T36_rho_mono (d : ℕ) (hd : 2 ≤ d) {i m : ℕ} (him : i ≤ m) : rhoStair d i ≤ rhoStair d m := by
  obtain ⟨hss, h1, hd2⟩ := T36_s_facts d hd
  have him' : (i : ℝ) ≤ m := by exact_mod_cast him
  unfold rhoStair
  set s := Real.sqrt (2 * (d : ℝ) - 1) with hs
  by_cases hm : (2 * (m : ℝ) - 1) ≤ s
  · have hi : (2 * (i : ℝ) - 1) ≤ s := by linarith
    simp [hm, hi]
  · rw [not_le] at hm
    rw [if_neg (not_le.mpr hm)]
    by_cases hi : (2 * (i : ℝ) - 1) ≤ s
    · rw [if_pos hi]
      have hy : (0 : ℝ) < 2 * m - 1 := by linarith
      rw [← sub_nonneg]
      have : (2 * (m : ℝ) - 1) + (2 * d - 1) / (2 * m - 1) - 2 * s =
          (2 * (m : ℝ) - 1 - s) ^ 2 / (2 * m - 1) := by
        field_simp
        nlinarith
      rw [this]; positivity
    · rw [not_le] at hi
      rw [if_neg (not_le.mpr hi)]
      have hx : (0 : ℝ) < 2 * i - 1 := by linarith
      have hy : (0 : ℝ) < 2 * m - 1 := by linarith
      rw [← sub_nonneg]
      have : (2 * (m : ℝ) - 1) + (2 * d - 1) / (2 * m - 1) - ((2 * (i : ℝ) - 1) + (2 * d - 1) / (2 * i - 1))
          = (2 * (m : ℝ) - 2 * i) * ((2 * m - 1) * (2 * i - 1) - (2 * d - 1)) / ((2 * m - 1) * (2 * i - 1)) := by
        field_simp
        ring
      rw [this]
      apply div_nonneg
      · apply mul_nonneg (by linarith)
        nlinarith
      · positivity

lemma T36_rho_le (d m : ℕ) (hd : 2 ≤ d) (hm : m ≤ d) : rhoStair d m ≤ 2 * d := by
  obtain ⟨hss, h1, hd2⟩ := T36_s_facts d hd
  have hm' : (m : ℝ) ≤ d := by exact_mod_cast hm
  unfold rhoStair
  set s := Real.sqrt (2 * (d : ℝ) - 1) with hs
  split_ifs with h
  · linarith
  · rw [not_le] at h
    have hy : (0 : ℝ) < 2 * m - 1 := by linarith
    rw [← sub_nonneg]
    have : 2 * (d : ℝ) - ((2 * (m : ℝ) - 1) + (2 * d - 1) / (2 * m - 1)) =
        ((2 * (m : ℝ) - 2) * (2 * d - 1 - (2 * m - 1))) / (2 * m - 1) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ hy.le
    apply mul_nonneg <;> linarith

lemma T36_rho_diff_le (d : ℕ) (hd : 2 ≤ d) {m : ℕ} (hm : mStar d ≤ m) :
    rhoStair d (m + 1) - rhoStair d m ≤ 4 := by
  obtain ⟨hss, h1, hd2⟩ := T36_s_facts d hd
  have hms : ((m : ℝ) + 1) > (Real.sqrt (2 * (d : ℝ) - 1) + 1) / 2 := by
    have := Nat.lt_floor_add_one ((Real.sqrt (2 * (d : ℝ) - 1) + 1) / 2)
    have h2 : ((mStar d : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    unfold mStar at h2
    linarith
  unfold rhoStair
  set s := Real.sqrt (2 * (d : ℝ) - 1) with hs
  push_cast
  have hx : s < 2 * ((m : ℝ) + 1) - 1 := by linarith
  rw [if_neg (not_le.mpr hx)]
  have hy : (0 : ℝ) < 2 * ((m : ℝ) + 1) - 1 := by linarith
  split_ifs with h
  · have : (2 * ((m : ℝ) + 1) - 1) + (2 * d - 1) / (2 * ((m : ℝ) + 1) - 1) - 2 * s =
        (2 * ((m : ℝ) + 1) - 1 - s) ^ 2 / (2 * ((m : ℝ) + 1) - 1) := by
      field_simp
      nlinarith
    rw [this, div_le_iff₀ hy]
    nlinarith
  · rw [not_le] at h
    have hy' : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
    have : (2 * ((m : ℝ) + 1) - 1) + (2 * d - 1) / (2 * ((m : ℝ) + 1) - 1) -
        ((2 * (m : ℝ) - 1) + (2 * d - 1) / (2 * m - 1)) =
        2 - 2 * (2 * d - 1) / ((2 * ((m : ℝ) + 1) - 1) * (2 * m - 1)) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ 2 * (2 * (d : ℝ) - 1) / ((2 * ((m : ℝ) + 1) - 1) * (2 * m - 1)) := by
      apply div_nonneg (by linarith) (by positivity)
    linarith

lemma T36_mStar_pos (d : ℕ) (hd : 2 ≤ d) : 1 ≤ mStar d := by
  obtain ⟨hss, h1, hd2⟩ := T36_s_facts d hd
  unfold mStar
  apply Nat.le_floor
  push_cast
  linarith


end T36_b

section T36_c
open Set Filter Topology
open scoped Manifold ContDiff


lemma T36_urysohn (s t : Set ℝ) (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ᶠ x in 𝓝ˢ s, g x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, g x = 1) := by
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℝ)) (M := ℝ)
    (n := (⊤ : ℕ∞)) hs ht hd
  refine ⟨f, ?_, h0, h1⟩
  have := f.contMDiff
  rwa [contMDiff_iff_contDiff] at this

lemma T36_smooth_of (f : smoothFun) : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) := f.2

lemma T36_carrier_inter (ν : smoothFun →ₗ[ℝ] ℝ) {A B : Set ℝ}
    (hA : IsClosed A ∧ VanishesNear ν A) (hB : IsClosed B ∧ VanishesNear ν B) :
    IsClosed (A ∩ B) ∧ VanishesNear ν (A ∩ B) := by
  refine ⟨hA.1.inter hB.1, fun f hf => ?_⟩
  rw [Filter.Eventually, mem_nhdsSet_iff_exists] at hf
  obtain ⟨W, hWo, hAB, hW⟩ := hf
  have hs : IsClosed (B \ W) := hB.1.sdiff hWo
  have ht : IsClosed (A \ W) := hA.1.sdiff hWo
  have hd : Disjoint (B \ W) (A \ W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxB, hxW⟩ ⟨hxA, _⟩
    exact hxW (hAB ⟨hxA, hxB⟩)
  obtain ⟨g, hg, hg0, hg1⟩ := T36_urysohn _ _ hs ht hd
  have hf' := T36_smooth_of f
  let fg : smoothFun := ⟨fun x => (f : ℝ → ℝ) x * g x, hf'.mul hg⟩
  let fh : smoothFun := ⟨fun x => (f : ℝ → ℝ) x * (1 - g x), hf'.mul (contDiff_const.sub hg)⟩
  have hsum : f = fg + fh := by
    apply Subtype.ext
    funext x
    show (f : ℝ → ℝ) x = (f : ℝ → ℝ) x * g x + (f : ℝ → ℝ) x * (1 - g x)
    ring
  have hfW : ∀ᶠ x in 𝓝ˢ W, (f : ℝ → ℝ) x = 0 := by
    have : W ∈ 𝓝ˢ W := hWo.mem_nhdsSet.mpr subset_rfl
    exact Filter.mem_of_superset this hW
  have h1 : ∀ᶠ x in 𝓝ˢ B, (fg : ℝ → ℝ) x = 0 := by
    have hsub : B ⊆ W ∪ (B \ W) := by
      intro x hx
      by_cases h : x ∈ W
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    refine Filter.Eventually.filter_mono (nhdsSet_mono hsub) ?_
    rw [nhdsSet_union, Filter.eventually_sup]
    refine ⟨hfW.mono fun x hx => ?_, hg0.mono fun x hx => ?_⟩
    · show (f : ℝ → ℝ) x * g x = 0
      rw [hx, zero_mul]
    · show (f : ℝ → ℝ) x * g x = 0
      rw [hx, mul_zero]
  have h2 : ∀ᶠ x in 𝓝ˢ A, (fh : ℝ → ℝ) x = 0 := by
    have hsub : A ⊆ W ∪ (A \ W) := by
      intro x hx
      by_cases h : x ∈ W
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    refine Filter.Eventually.filter_mono (nhdsSet_mono hsub) ?_
    rw [nhdsSet_union, Filter.eventually_sup]
    refine ⟨hfW.mono fun x hx => ?_, hg1.mono fun x hx => ?_⟩
    · show (f : ℝ → ℝ) x * (1 - g x) = 0
      rw [hx, zero_mul]
    · show (f : ℝ → ℝ) x * (1 - g x) = 0
      rw [hx, sub_self, mul_zero]
  rw [hsum, map_add, hB.2 fg h1, hA.2 fh h2, add_zero]

lemma T36_carrier_finite (ν : smoothFun →ₗ[ℝ] ℝ) {ι : Type*} (t : ι → Set ℝ)
    (ht : ∀ i, IsClosed (t i) ∧ VanishesNear ν (t i)) (B0 : Set ℝ)
    (hB0 : IsClosed B0 ∧ VanishesNear ν B0) (u : Finset ι) :
    IsClosed (B0 ∩ ⋂ i ∈ u, t i) ∧ VanishesNear ν (B0 ∩ ⋂ i ∈ u, t i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using hB0
  | insert a u ha ih =>
    have e : B0 ∩ (⋂ i ∈ insert a u, t i) = (B0 ∩ ⋂ i ∈ u, t i) ∩ t a := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [e]
    exact T36_carrier_inter ν ih (ht a)

lemma T36_icc_carrier (ν : smoothFun →ₗ[ℝ] ℝ) (c K : ℝ) (m : ℕ) (hK : 0 < K)
    (hbd : ∀ f : smoothFun, |ν f| ≤ c * cNorm m f (-K) K) :
    IsClosed (Icc (-K) K) ∧ VanishesNear ν (Icc (-K) K) := by
  refine ⟨isClosed_Icc, fun f hf => ?_⟩
  rw [Filter.Eventually, mem_nhdsSet_iff_exists] at hf
  obtain ⟨U, hUo, hIU, hU⟩ := hf
  have hzero : ∀ j : ℕ, ∀ x ∈ Icc (-K) K, iteratedDeriv j (f : ℝ → ℝ) x = 0 := by
    intro j x hx
    have hev : (f : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (hUo.mem_nhds (hIU hx)) hU
    rw [hev.iteratedDeriv_eq j]
    simp
  have hc : cNorm m f (-K) K = 0 := by
    unfold cNorm
    apply Finset.sum_eq_zero
    intro j _
    unfold supOn
    have : (fun x => |iteratedDeriv j (f : ℝ → ℝ) x|) '' Icc (-K) K = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [hzero j x hx]
      · rintro rfl
        exact ⟨0, ⟨by linarith, hK.le⟩, by simp [hzero j 0 ⟨by linarith, hK.le⟩]⟩
    rw [this, csSup_singleton]
  have := hbd f
  rw [hc, mul_zero] at this
  exact abs_nonpos_iff.mp this

/-- A compactly supported distribution whose support lies in `F` kills every smooth function
vanishing on an open set containing `F`. -/
theorem T36_kills (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) (F : Set ℝ)
    (hF : supp ν ⊆ F) (U : Set ℝ) (hU : IsOpen U) (hFU : F ⊆ U) (f : smoothFun)
    (hf : ∀ x ∈ U, (f : ℝ → ℝ) x = 0) : ν f = 0 := by
  obtain ⟨c, K, m, hc, hK, hbd⟩ := hν
  let C : Set (Set ℝ) := {A | IsClosed A ∧ VanishesNear ν A}
  have hcomp : IsCompact (Icc (-K) K \ U) := isCompact_Icc.diff hU
  have hfin : ∃ u : Finset C, ¬ ((Icc (-K) K \ U) ∩ ⋂ i ∈ u, (i : Set ℝ)).Nonempty := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx1, hx2⟩ := hcomp.inter_iInter_nonempty (fun i : C => (i : Set ℝ))
      (fun i => i.2.1) hcon
    have hxs : x ∈ supp ν := by
      show x ∈ ⋂₀ C
      rw [Set.mem_sInter]
      intro A hA
      have := Set.mem_iInter.mp hx2 ⟨A, hA⟩
      exact this
    exact hx1.2 (hFU (hF hxs))
  obtain ⟨u, hu⟩ := hfin
  have hB := T36_carrier_finite ν (fun i : C => (i : Set ℝ)) (fun i => i.2)
    (Icc (-K) K) (T36_icc_carrier ν c K m hK hbd) u
  have hBU : Icc (-K) K ∩ ⋂ i ∈ u, (i : Set ℝ) ⊆ U := by
    intro x hx
    by_contra hxU
    exact hu ⟨x, ⟨hx.1, hxU⟩, hx.2⟩
  apply hB.2 f
  exact Filter.mem_of_superset (hU.mem_nhdsSet.mpr hBU) hf


end T36_c

section T36_d
open Set Filter Topology
open scoped ComplexOrder InnerProductSpace


section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma T36_trace_nonneg (T : E →L[ℂ] E) (hT : 0 ≤ T) :
    0 ≤ (LinearMap.trace ℂ E (T : E →ₗ[ℂ] E)).re := by
  have hp : (T : E →ₗ[ℂ] E).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).mp hT
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hp.re_inner_nonneg_right _

lemma T36_trace_ge_one (T : E →L[ℂ] E) (hT : 0 ≤ T) (v : E) (hv : ‖v‖ = 1) (hTv : T v = v) :
    1 ≤ (LinearMap.trace ℂ E (T : E →ₗ[ℂ] E)).re := by
  classical
  have hp : (T : E →ₗ[ℂ] E).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).mp hT
  have hon : Orthonormal ℂ ((↑) : ({v} : Set E) → E) := by
    rw [orthonormal_iff_ite]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp [inner_self_eq_norm_sq_to_K, hv]
  obtain ⟨u, b, hvu, hb⟩ := hon.exists_orthonormalBasis_extension
  have hvu' : v ∈ u := hvu rfl
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  have := Finset.single_le_sum (f := fun i : u => (⟪b i, (T : E →ₗ[ℂ] E) (b i)⟫_ℂ).re)
    (fun i _ => hp.re_inner_nonneg_right _) (Finset.mem_univ ⟨v, hvu'⟩)
  refine le_trans ?_ this
  have hbv : b ⟨v, hvu'⟩ = v := by rw [hb]
  simp [hbv, hTv, inner_self_eq_norm_sq_to_K, hv]

lemma T36_aeval_eigen (A : E →L[ℂ] E) (z : ℂ) (v : E) (hv : A v = z • v) (p : Polynomial ℂ) :
    (Polynomial.aeval A p) v = p.eval z • v := by
  have hpow : ∀ n : ℕ, (A ^ n) v = z ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, ContinuousLinearMap.add_apply, hp, hq, add_smul]
  | monomial n c =>
    simp [Polynomial.aeval_monomial, hpow, smul_smul, mul_comm]

lemma T36_cfc_eigen (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (f : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ spectrum ℂ A) (v : E) (hv : A v = z • v) :
    (cfc f A) v = f z • v := by
  classical
  have hfin : (spectrum ℂ A).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  set p : Polynomial ℂ := Lagrange.interpolate hfin.toFinset id f with hp
  have hpe : ∀ w ∈ spectrum ℂ A, p.eval w = f w := by
    intro w hw
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (r := f)
      (Function.injective_id.injOn) (hfin.mem_toFinset.mpr hw)
    simpa [hp] using this
  have h1 : cfc f A = cfc (fun x : ℂ => p.eval x) A := by
    apply cfc_congr
    intro w hw
    exact (hpe w hw).symm
  have hn : IsStarNormal A := hA.isStarNormal
  rw [h1, cfc_polynomial p A, T36_aeval_eigen A z v hv, hpe z hz]

end Abstract


end T36_d

section T36_e
open Set Filter Topology
open scoped ComplexOrder InnerProductSpace


lemma T36_markov (d N : ℕ) (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) (χ : ℝ → ℝ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (α : ℝ) (hα : 0 < α)
    (h1 : ∀ x, α ≤ |x| → χ x = 1) :
    0 ≤ trN N (fnCalc χ (adjPerp σ)) ∧
      (α ≤ ‖adjPerp σ‖ → 1 ≤ (N : ℝ) * trN N (fnCalc χ (adjPerp σ))) := by
  have hA : IsSelfAdjoint (adjPerp σ) := T36_isSelfAdjoint_sum d (sModel σ)
  set A := adjPerp σ with hAdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 ≤ fnCalc χ A := by
    unfold fnCalc
    apply cfc_nonneg
    intro x _
    exact Complex.zero_le_real.mpr (h01 _).1
  have htr := T36_trace_nonneg (fnCalc χ A) hpos
  refine ⟨div_nonneg htr hNpos.le, fun hαA => ?_⟩
  have hmul : (N : ℝ) * trN N (fnCalc χ A) =
      (LinearMap.trace ℂ _ ((fnCalc χ A : OnesPerp N →L[ℂ] OnesPerp N) :
        OnesPerp N →ₗ[ℂ] OnesPerp N)).re := by
    unfold trN
    field_simp
  rw [hmul]
  have hne : A ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hαA
    linarith
  have : Nontrivial (OnesPerp N →L[ℂ] OnesPerp N) := ⟨⟨A, 0, hne⟩⟩
  obtain ⟨z, hz, hzn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty A)
  have hzn2 := ContinuousLinearMap.spectralRadius_eq_nnnorm (𝕜 := ℂ) (T := A) hA
  have hzn := hzn.trans hzn2
  have hzn' : ‖z‖ = ‖A‖ := by
    have := ENNReal.coe_inj.mp hzn
    simpa using congrArg NNReal.toReal this
  have hzre : z = (z.re : ℂ) := hA.mem_spectrum_eq_re hz
  have hχz : χ z.re = 1 := by
    apply h1
    have : |z.re| = ‖z‖ := by
      conv_rhs => rw [hzre]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [this, hzn']
    exact hαA
  have hev : Module.End.HasEigenvalue (A : Module.End ℂ (OnesPerp N)) z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, ← ContinuousLinearMap.spectrum_eq]
    exact hz
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hAv : A v = z • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set u : OnesPerp N := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn)]
    field_simp
  have hAu : A u = z • u := by
    rw [hu, map_smul, hAv, smul_comm]
  have hTu : fnCalc χ A u = u := by
    unfold fnCalc
    rw [T36_cfc_eigen A hA _ z hz u hAu]
    rw [hzre, show (z.re : ℂ).re = z.re from Complex.ofReal_re _, hχz]
    simp
  exact T36_trace_ge_one _ hpos u hun hTu


end T36_e

section T36_f
open Set Filter Topology


lemma T36_prob_le_exp (d N : ℕ) (hN : 1 ≤ N) (χ : ℝ → ℝ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (α : ℝ) (hα : 0 < α) (h1 : ∀ x, α ≤ |x| → χ x = 1) :
    uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => α ≤ ‖adjPerp σ‖) ≤
      (N : ℝ) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (fnCalc χ (adjPerp σ))) := by
  classical
  unfold uniformProb uniformExp
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.card_filter]
  push_cast
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ hcard.le
  apply Finset.sum_le_sum
  intro σ _
  obtain ⟨h0, h2⟩ := T36_markov d N hN σ χ h01 α hα h1
  split_ifs with h
  · exact h2 h
  · exact mul_nonneg (Nat.cast_nonneg _) h0


lemma T36_nu_zero (d : ℕ) (hd : 2 ≤ d) (ν : smoothFun →ₗ[ℝ] ℝ) (i m : ℕ) (hi : i ≤ m)
    (hmd : m ≤ d) (hνi : IsCSDistribution ν)
    (hext : ∀ h : Polynomial ℝ, ν (polyFun h) = nu (T36_P d) i h) (ε : ℝ) (hε : 0 < ε)
    (χ : smoothFun) (hχ : ∀ x, |x| ≤ rhoStair d m + ε / 2 → (χ : ℝ → ℝ) x = 0) : ν χ = 0 := by
  have hsupp := supp_subset_Icc_rhoStair_of_extends_nuAdj d hd i (hi.trans hmd) ν hνi
    (fun h => by rw [hext h, T36_nu_eq])
  have hρ := T36_rho_mono d hd hi
  have hF : supp ν ⊆ Icc (-rhoStair d m) (rhoStair d m) := by
    intro x hx
    have := hsupp hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  refine T36_kills ν hνi (Icc (-rhoStair d m) (rhoStair d m)) hF
    {x : ℝ | |x| < rhoStair d m + ε / 2} (isOpen_lt continuous_abs continuous_const) ?_ χ ?_
  · intro x hx
    have : |x| ≤ rhoStair d m := abs_le.mpr ⟨hx.1, hx.2⟩
    show |x| < _
    linarith
  · intro x hx
    exact hχ x (le_of_lt hx)

lemma T36_lower (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : mStar d ≤ m) (hmd : m ≤ d - 1)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < rhoStair d (m + 1) - rhoStair d m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ m ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖) := by
  have h := prob_norm_adjPerp_ge_of_lt_rhoStair d hd (m + 1) (by omega) (by omega)
    (rhoStair d m + ε) (by linarith) η hη
  simpa using h


end T36_f

section T36_g
open Set Filter Topology


lemma T36_log_facts (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) :
    let L := Real.log (2 * (d : ℝ) / ε)
    let u := Real.log (2 * Real.exp 1 / ε)
    1 / 4 ≤ u ∧ L + 1 ≤ (4 * Real.log d + 1) * u := by
  intro L u
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL : L = Real.log 2 + Real.log d - Real.log ε := by
    show Real.log (2 * (d : ℝ) / ε) = _
    rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by norm_num) hd0.ne']
  have hu : u = Real.log 2 + 1 - Real.log ε := by
    show Real.log (2 * Real.exp 1 / ε) = _
    rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
      Real.log_exp]
  have h4 : Real.log ε ≤ 2 * Real.log 2 := by
    have := Real.log_le_log hε hε4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat] at this
  have hu4 : 1 / 4 ≤ u := by rw [hu]; linarith
  refine ⟨hu4, ?_⟩
  rw [hL]
  have : Real.log 2 + Real.log d - Real.log ε + 1 = Real.log d + u := by rw [hu]; ring
  rw [this]
  nlinarith

theorem T36_upper (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ m : ℕ, mStar d ≤ m → m ≤ d - 1 → ∀ ε : ℝ, 0 < ε →
        ε < rhoStair d (m + 1) - rhoStair d m → ∀ N : ℕ, 1 ≤ N →
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖) ≤
          C / ((N : ℝ) ^ m * ε ^ (4 * (m + 1))) * Real.log (2 * Real.exp 1 / ε) := by
  obtain ⟨C0, h410⟩ := exists_testFunction
  obtain ⟨C7, h71⟩ := exists_csDistribution_abs_expTr_sub_le
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  set B : ℝ := max 1 (4 * (1 + Real.log d) * |C0| * (4 * d) * (2 * d)) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨|C7| * Real.exp 1 * B ^ (4 * d) * (4 * Real.log d + 1), ?_⟩
  intro m hm hmd ε hε hε2 N hN
  have hm1 : 1 ≤ m := (T36_mStar_pos d hd).trans hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ := T36_rho_pos d m hd
  have hρle : rhoStair d (m + 1) ≤ 2 * d := T36_rho_le d (m + 1) hd (by omega)
  have hK : rhoStair d m + ε < 2 * (d : ℝ) := by linarith
  have hε4 : ε ≤ 4 := by have := T36_rho_diff_le d hd hm; linarith
  obtain ⟨χ, hχs, hχ01, hχ0, hχ1, hχn⟩ :=
    h410 (4 * (m + 1)) (2 * (d : ℝ)) (rhoStair d m) ε (by omega) (by positivity) hρ hε hK
  have h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => hχ01 x
  have hprob := T36_prob_le_exp d N hN χ h01 (rhoStair d m + ε) (by positivity) hχ1
  rw [← T36_expTr d N χ hχs.continuous] at hprob
  obtain ⟨ν, hν, hbd⟩ := h71 (q₀ := 1) (T36_P d) (T36_P_selfAdjoint d) (T36_P_degree d)
  -- parameters
  have hKε : 1 < 2 * (d : ℝ) / ε := by
    rw [one_lt_div hε]; linarith
  set L := Real.log (2 * (d : ℝ) / ε) with hLdef
  have hL : 0 < L := Real.log_pos hKε
  set β : ℝ := 1 + 1 / L with hβdef
  have hβ : 1 < β := by have : 0 < 1 / L := by positivity
                        linarith
  have hconj : conjExp β = L + 1 := by
    unfold conjExp
    have : 1 - 1 / β = 1 / (L + 1) := by
      rw [hβdef]; field_simp; ring
    rw [this]; field_simp
  -- vanishing of the lower coefficients
  have hsum : ∑ i ∈ Finset.range (m + 1), ν i ⟨χ, hχs⟩ / (N : ℝ) ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [T36_nu_zero d hd (ν i) i m hi' (by omega) (hν i).1 (fun h => by rw [(hν i).2 h]) ε hε
      ⟨χ, hχs⟩ hχ0, zero_div]
  have key0 := hbd N (m + 1) hN (by omega) β hβ ⟨χ, hχs⟩
  rw [T36_fullNorm, hsum, sub_zero] at key0
  have key : |expTr (T36_P d) N χ| ≤
      C7 * (4 * ((1 : ℕ) : ℝ) * (1 + Real.log d)) ^ (4 * (m + 1)) / (N : ℝ) ^ (m + 1) * conjExp β *
        lpNormCircle β (iteratedDeriv (4 * (m + 1) + 1) (fun θ => χ (2 * (d : ℝ) * Real.cos θ))) :=
    key0
  have hlp := hχn β hβ
  rw [hconj] at hlp
  -- bounding the rpow
  have hrpow : (2 * (d : ℝ) / ε) ^ (((4 * (m + 1) : ℕ) : ℝ) + 1 / (L + 1)) ≤
      (2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1 := by
    have hpos : 0 < 2 * (d : ℝ) / ε := by positivity
    rw [Real.rpow_add hpos, Real.rpow_natCast]
    gcongr
    rw [Real.rpow_def_of_pos hpos, ← hLdef]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  have hlp' : lpNormCircle β (iteratedDeriv (4 * (m + 1) + 1) (fun θ => χ (2 * (d : ℝ) * Real.cos θ))) ≤
      (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) *
        ((2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1) := by
    refine hlp.trans ?_
    have h1 : (C0 * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) ≤
        (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) := by
      have : |C0 * ((4 * (m + 1) : ℕ) : ℝ)| = |C0| * ((4 * (m + 1) : ℕ) : ℝ) := by
        rw [abs_mul, Nat.abs_cast]
      calc (C0 * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1))
          ≤ |(C0 * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1))| := le_abs_self _
        _ = _ := by rw [abs_pow, this]
    exact mul_le_mul h1 hrpow (by positivity) (by positivity)
  obtain ⟨hu4, hLu⟩ := T36_log_facts d hd ε hε hε4
  have hlp0 : 0 ≤ lpNormCircle β (iteratedDeriv (4 * (m + 1) + 1)
      (fun θ => χ (2 * (d : ℝ) * Real.cos θ))) := ENNReal.toReal_nonneg
  have hM : ((4 * (m + 1) : ℕ) : ℝ) ≤ 4 * d := by
    have : 4 * (m + 1) ≤ 4 * d := by omega
    exact_mod_cast this
  have hbase : 4 * (1 + Real.log d) * (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) * (2 * (d : ℝ)) ≤ B := by
    refine le_trans ?_ (le_max_right _ _)
    have h0 : 0 ≤ 4 * (1 + Real.log d) := by positivity
    have : |C0| * ((4 * (m + 1) : ℕ) : ℝ) ≤ |C0| * (4 * d) := by gcongr
    calc 4 * (1 + Real.log d) * (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) * (2 * (d : ℝ))
        ≤ 4 * (1 + Real.log d) * (|C0| * (4 * d)) * (2 * (d : ℝ)) := by gcongr
      _ = _ := by ring
  have hpowB : (4 * (1 + Real.log d) * (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) * (2 * (d : ℝ))) ^
      (4 * (m + 1)) ≤ B ^ (4 * d) :=
    (pow_le_pow_left₀ (by positivity) hbase _).trans (pow_le_pow_right₀ hB1 (by omega))
  have hεM : 0 < ε ^ (4 * (m + 1)) := by positivity
  have hNm : 0 < (N : ℝ) ^ m := by positivity
  have key2 : |expTr (T36_P d) N χ| ≤ |C7| * (4 * (1 + Real.log d)) ^ (4 * (m + 1)) /
      (N : ℝ) ^ (m + 1) * (L + 1) * ((|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) *
        ((2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1)) := by
    rw [hconj] at key
    refine key.trans ?_
    simp only [Nat.cast_one, mul_one]
    have hA : 0 ≤ (4 * (1 + Real.log d)) ^ (4 * (m + 1)) / (N : ℝ) ^ (m + 1) * (L + 1) := by
      positivity
    calc C7 * (4 * (1 + Real.log d)) ^ (4 * (m + 1)) / (N : ℝ) ^ (m + 1) * (L + 1) *
          lpNormCircle β (iteratedDeriv (4 * (m + 1) + 1) (fun θ => χ (2 * (d : ℝ) * Real.cos θ)))
        = C7 * ((4 * (1 + Real.log d)) ^ (4 * (m + 1)) / (N : ℝ) ^ (m + 1) * (L + 1)) *
          lpNormCircle β (iteratedDeriv (4 * (m + 1) + 1) (fun θ => χ (2 * (d : ℝ) * Real.cos θ))) := by
          ring
      _ ≤ |C7| * ((4 * (1 + Real.log d)) ^ (4 * (m + 1)) / (N : ℝ) ^ (m + 1) * (L + 1)) *
          ((|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) *
            ((2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1)) := by
          apply mul_le_mul _ hlp' hlp0 (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self C7) hA
      _ = _ := by ring
  have hLpos : 0 ≤ L + 1 := by linarith
  have eqn : (N : ℝ) * (|C7| * (4 * (1 + Real.log d)) ^ (4 * (m + 1)) /
      (N : ℝ) ^ (m + 1) * (L + 1) * ((|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) *
        ((2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1))) =
      |C7| * Real.exp 1 * (L + 1) * (4 * (1 + Real.log d) * (|C0| * ((4 * (m + 1) : ℕ) : ℝ)) *
        (2 * (d : ℝ))) ^ (4 * (m + 1)) / ((N : ℝ) ^ m * ε ^ (4 * (m + 1))) := by
    simp only [mul_pow, div_pow, pow_succ]
    field_simp
  calc uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖)
      ≤ (N : ℝ) * expTr (T36_P d) N χ := hprob
    _ ≤ (N : ℝ) * |expTr (T36_P d) N χ| := mul_le_mul_of_nonneg_left (le_abs_self _) hNpos.le
    _ ≤ (N : ℝ) * (|C7| * (4 * (1 + Real.log d)) ^ (4 * (m + 1)) /
      (N : ℝ) ^ (m + 1) * (L + 1) * ((|C0| * ((4 * (m + 1) : ℕ) : ℝ)) ^ (4 * (m + 1)) *
        ((2 * (d : ℝ) / ε) ^ (4 * (m + 1)) * Real.exp 1))) :=
        mul_le_mul_of_nonneg_left key2 hNpos.le
    _ = _ := eqn
    _ ≤ |C7| * Real.exp 1 * (L + 1) * B ^ (4 * d) / ((N : ℝ) ^ m * ε ^ (4 * (m + 1))) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hpowB (by positivity)
    _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        have hB0 : 0 ≤ |C7| * Real.exp 1 * B ^ (4 * d) := by positivity
        calc |C7| * Real.exp 1 * (L + 1) * B ^ (4 * d)
            = (|C7| * Real.exp 1 * B ^ (4 * d)) * (L + 1) := by ring
          _ ≤ (|C7| * Real.exp 1 * B ^ (4 * d)) * ((4 * Real.log d + 1) * Real.log (2 * Real.exp 1 / ε)) :=
              mul_le_mul_of_nonneg_left hLu hB0
          _ = _ := by ring


end T36_g

section T36_final
open Filter

theorem prob_norm_adjPerp_ge_rhoStair_dev (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ,
      (∀ m : ℕ, mStar d ≤ m → m ≤ d - 1 → ∀ ε : ℝ, 0 < ε →
        ε < rhoStair d (m + 1) - rhoStair d m → ∀ N : ℕ, 1 ≤ N →
        uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖) ≤
          C / ((N : ℝ) ^ m * ε ^ (4 * (m + 1))) * Real.log (2 * Real.exp 1 / ε)) ∧
      (∀ m : ℕ, mStar d ≤ m → m ≤ d - 1 → ∀ ε : ℝ, 0 < ε →
        ε < rhoStair d (m + 1) - rhoStair d m → ∀ η : ℝ, 0 < η →
        ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ m ≤
          uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => rhoStair d m + ε ≤ ‖adjPerp σ‖)) := by
  obtain ⟨C, hC⟩ := T36_upper d hd
  exact ⟨C, hC, fun m hm hmd ε hε hε2 η hη => T36_lower d hd m hm hmd ε hε hε2 η hη⟩
end T36_final

end StrongConv

end

theorem solution : type_of% @StrongConv.prob_norm_adjPerp_ge_rhoStair_dev := @StrongConv.prob_norm_adjPerp_ge_rhoStair_dev
