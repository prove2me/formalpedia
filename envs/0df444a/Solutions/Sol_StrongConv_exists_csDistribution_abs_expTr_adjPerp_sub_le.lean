-- Prove2me | solution 1 for StrongConv.exists_csDistribution_abs_expTr_adjPerp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:04:58.288315+00:00
-- url     : https://prove2.me/submissions/656acd45-ba5c-4181-9405-55c4ab552c49

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_sub_le
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_tfae_extends_csDistribution

open Polynomial Filter Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace StrongConv

def L81_P (d : ℕ) : NCPoly 1 d :=
  ∑ l : Fin d ⊕ Fin d, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)

lemma L81_tensorOp_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (T : H →L[ℂ] H) : tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x i
  simp [tensorOp]

lemma L81_tensorOp_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  ext x i
  simp [tensorOp, add_smul, Finset.sum_add_distrib]

lemma L81_sum_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) (s : Finset (Fin d ⊕ Fin d)) :
    (∑ l ∈ s, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)).sum
      (fun w A => tensorOp A (wordOp u w)) =
      ∑ l ∈ s, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      Finsupp.sum_add_index' (fun w => L81_tensorOp_zero _) (fun w A B => L81_tensorOp_add A B _), ih,
      Finsupp.sum_single_index (L81_tensorOp_zero _)]
    simp [wordOp]

lemma L81_eval_P {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (L81_P d).eval u = ∑ l : Fin d ⊕ Fin d, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) :=
  L81_sum_single d u Finset.univ

/-- the identification `PiLp 2 (Fin 1 → H) ≃ H` -/
def L81_E (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
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

lemma L81_tensorOp_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) T = (L81_E H).symm.conjStarAlgEquiv T := by
  ext x i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [tensorOp, L81_E]
  rfl

lemma L81_eval_P' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (L81_P d).eval u = (L81_E H).symm.conjStarAlgEquiv (∑ i, (u i + star (u i))) := by
  rw [L81_eval_P]
  simp only [L81_tensorOp_one, ← map_sum, Fintype.sum_sum_type, letterOp, Finset.sum_add_distrib]

lemma L81_isSelfAdjoint_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) :=
  isSelfAdjoint_sum _ fun i _ => IsSelfAdjoint.add_star_self (u i)

lemma L81_fnCalc_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : ℝ → ℝ) (hh : Continuous h) (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    fnCalc h ((L81_E H).symm.conjStarAlgEquiv a) =
      (L81_E H).symm.conjStarAlgEquiv (fnCalc h a) := by
  have hn : IsStarNormal a := ha.isStarNormal
  unfold fnCalc
  have hc : Continuous (fun z : ℂ => ((h z.re : ℝ) : ℂ)) := by fun_prop
  have hcont : Continuous (L81_E H).symm.conjStarAlgEquiv := by
    have : (fun T : H →L[ℂ] H => (L81_E H).symm.conjStarAlgEquiv T) =
        fun T => ((L81_E H).symm.toContinuousLinearEquiv : _ →L[ℂ] _) ∘L T ∘L
          ((L81_E H).toContinuousLinearEquiv : _ →L[ℂ] _) := rfl
    show Continuous (fun T : H →L[ℂ] H => (L81_E H).symm.conjStarAlgEquiv T)
    rw [this]
    fun_prop
  exact (StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) (L81_E H).symm.conjStarAlgEquiv
      (fun z : ℂ => ((h z.re : ℝ) : ℂ)) a hc.continuousOn hcont hn
      (ha.map _).isStarNormal).symm

lemma L81_trace_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : H →L[ℂ] H) :
    LinearMap.trace ℂ _ (((L81_E H).symm.conjStarAlgEquiv a : PiLp 2 (fun _ : Fin 1 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 1 => H)) : PiLp 2 (fun _ : Fin 1 => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin 1 => H)) =
      LinearMap.trace ℂ _ (a : H →ₗ[ℂ] H) := by
  have := LinearMap.trace_conj' (a : H →ₗ[ℂ] H) (L81_E H).symm.toLinearEquiv
  rw [← this]
  congr 1

theorem L81_trDN_eval (d N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (h : ℝ → ℝ) (hh : Continuous h) :
    trDN 1 N (fnCalc h ((L81_P d).eval (sModel σ))) = trN N (fnCalc h (adjPerp σ)) := by
  rw [L81_eval_P' d (sModel σ)]
  have hsa : IsSelfAdjoint (adjPerp σ) := L81_isSelfAdjoint_sum d (sModel σ)
  have := L81_fnCalc_conj h hh (adjPerp σ) hsa
  have e : (∑ i, (sModel σ i + star (sModel σ i))) = adjPerp σ := rfl
  rw [e, this]
  unfold trDN trN
  rw [L81_trace_conj]
  simp


/-! ## Part A: facts about `P` -/

lemma L81_P_apply (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    L81_P d w = if w.length = 1 then 1 else 0 := by
  classical
  unfold L81_P
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

lemma L81_wordStar_length (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    (NCPoly.wordStar w).length = w.length := by
  simp [NCPoly.wordStar, FreeMonoid.length]

lemma L81_P_selfAdjoint (d : ℕ) : (L81_P d).IsSelfAdjoint := by
  intro w
  rw [L81_P_apply, L81_P_apply, L81_wordStar_length]
  split_ifs <;> simp

lemma L81_P_degree (d : ℕ) : (L81_P d).degree ≤ 1 := by
  unfold NCPoly.degree
  apply Finset.sup_le
  intro w hw
  rw [Finsupp.mem_support_iff, L81_P_apply] at hw
  by_contra hc
  exact hw (if_neg (by omega))

lemma L81_norm_unitary_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
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

lemma L81_norm_eval_le (d : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖(L81_P d).eval u‖ ≤ 2 * d := by
  rw [L81_eval_P', StarAlgEquiv.norm_map]
  calc ‖∑ i, (u i + star (u i))‖ ≤ ∑ i, ‖u i + star (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖u i + star (u i)‖ ≤ ‖u i‖ + ‖star (u i)‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_star]; linarith [hu i]
    _ = 2 * d := by simp [mul_comm]

lemma L81_fullNorm (d : ℕ) : (L81_P d).fullNorm = 2 * d := by
  unfold NCPoly.fullNorm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨1, fun _ => 1, ?_⟩
    rw [L81_eval_P', StarAlgEquiv.norm_map]
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
    exact L81_norm_eval_le d _ fun i => L81_norm_unitary_le (U i)



lemma L81_pow_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    (∑ i, (u i + star (u i))) ^ p =
      ∑ x : Fin p → Fin d ⊕ Fin d, wordEval u (List.ofFn fun j => some (x j)) := by
  induction p with
  | zero => simp [wordEval]
  | succ p ih =>
    have key : ∀ F : (Fin (p + 1) → Fin d ⊕ Fin d) → (H →L[ℂ] H),
        ∑ x, F x = ∑ l : Fin d ⊕ Fin d, ∑ y : Fin p → Fin d ⊕ Fin d, F (Fin.cons l y) := by
      intro F
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p + 1) => Fin d ⊕ Fin d))
        (fun z => F (Fin.cons z.1 z.2)) F (fun _ => rfl)).symm
    rw [pow_succ', ih, key, Finset.sum_mul, Fintype.sum_sum_type]
    have hw : ∀ (l : Fin d ⊕ Fin d) (y : Fin p → Fin d ⊕ Fin d),
        wordEval u (List.ofFn fun j => some ((Fin.cons l y : Fin (p + 1) → Fin d ⊕ Fin d) j)) =
          letterOp u l * wordEval u (List.ofFn fun j => some (y j)) := by
      intro l y
      simp [wordEval, List.ofFn_succ]
    simp only [hw, ← Finset.mul_sum, add_mul, Finset.sum_add_distrib]
    simp [letterOp]


lemma L81_trN_sum {N : ℕ} {ι : Type*} (s : Finset ι) (T : ι → OnesPerp N →L[ℂ] OnesPerp N) :
    trN N (∑ x ∈ s, T x) = ∑ x ∈ s, trN N (T x) := by
  unfold trN
  rw [← Finset.sum_div]
  congr 1
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum, Complex.re_sum]

lemma L81_trN_smul {N : ℕ} (r : ℝ) (T : OnesPerp N →L[ℂ] OnesPerp N) :
    trN N ((r : ℂ) • T) = r * trN N T := by
  unfold trN
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, mul_div_assoc]

lemma L81_uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, uniformExp (f i) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

lemma L81_uniformExp_mul {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformExp (fun x => r * f x) = r * uniformExp f := by
  unfold uniformExp
  rw [← Finset.mul_sum, mul_div_assoc]

lemma L81_tau_sum {d : ℕ} {ι : Type*} (s : Finset ι) (T : ι → L2Free d →L[ℂ] L2Free d) :
    tau (∑ x ∈ s, T x) = ∑ x ∈ s, tau (T x) := by
  unfold tau
  simp [ContinuousLinearMap.sum_apply, inner_sum]

lemma L81_tau_smul {d : ℕ} (r : ℂ) (T : L2Free d →L[ℂ] L2Free d) :
    tau (r • T) = r * tau T := by
  unfold tau
  simp [inner_smul_right]

lemma L81_tendsto_pow (d p : ℕ) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (adjPerp σ ^ p))) atTop (𝓝 (tau (adjFree d ^ p)).re) := by
  have h1 : ∀ (N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)), trN N (adjPerp σ ^ p) =
      ∑ x : Fin p → Fin d ⊕ Fin d, trN N (wordEval (sModel σ) (List.ofFn fun j => some (x j))) := by
    intro N σ
    rw [← L81_trN_sum]
    congr 1
    exact L81_pow_expand d (sModel σ) p
  have h2 : tau (adjFree d ^ p) =
      ∑ x : Fin p → Fin d ⊕ Fin d, tau (wordEval (sLimit d) (List.ofFn fun j => some (x j))) := by
    rw [← L81_tau_sum]
    congr 1
    exact L81_pow_expand d (sLimit d) p
  simp only [h1, h2, L81_uniformExp_sum, Complex.re_sum]
  apply tendsto_finsetSum
  intro x _
  have := (Complex.continuous_re.tendsto _).comp
    (tendsto_uniformExp_trN_wordEval d (List.ofFn fun j => some (x j)))
  simpa [Function.comp_def] using this

lemma L81_fnCalc_poly {A : Type*} [CStarAlgebra A] (a : A) (ha : IsSelfAdjoint a) (h : ℝ[X]) :
    fnCalc (fun x => h.eval x) a =
      ∑ k ∈ Finset.range (h.natDegree + 1), ((h.coeff k : ℝ) : ℂ) • a ^ k := by
  have hC := cfc_polynomial (R := ℂ) (h.map (algebraMap ℝ ℂ)) a
  have e : fnCalc (fun x => h.eval x) a =
      cfc (fun x : ℂ => (h.map (algebraMap ℝ ℂ)).eval x) a := by
    unfold fnCalc
    apply cfc_congr
    intro z hz
    have := ha.mem_spectrum_eq_re hz
    simp only
    conv_rhs => rw [this]
    have h2 := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (z.re) (p := h)
    rw [Polynomial.eval_map]
    exact h2.symm
  rw [e, hC, Polynomial.aeval_eq_sum_range, Polynomial.natDegree_map_eq_of_injective
    (algebraMap ℝ ℂ).injective]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Polynomial.coeff_map]

theorem L81_tendsto_poly (d : ℕ) (h : ℝ[X]) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => h.eval x) (adjPerp σ)))) atTop
      (𝓝 (tau (fnCalc (fun x => h.eval x) (adjFree d))).re) := by
  have hsa : ∀ (N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)), IsSelfAdjoint (adjPerp σ) := fun N σ =>
    L81_isSelfAdjoint_sum d (sModel σ)
  have hsaF : IsSelfAdjoint (adjFree d) :=
    L81_isSelfAdjoint_sum d (sLimit d)
  have e1 : ∀ (N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)),
      trN N (fnCalc (fun x => h.eval x) (adjPerp σ)) =
        ∑ k ∈ Finset.range (h.natDegree + 1), h.coeff k * trN N (adjPerp σ ^ k) := by
    intro N σ
    rw [L81_fnCalc_poly _ (hsa N σ), L81_trN_sum]
    exact Finset.sum_congr rfl fun k _ => L81_trN_smul _ _
  rw [L81_fnCalc_poly _ hsaF, L81_tau_sum, Complex.re_sum]
  simp only [e1, L81_uniformExp_sum, L81_uniformExp_mul, L81_tau_smul, Complex.re_ofReal_mul]
  apply tendsto_finsetSum
  intro k _
  exact (L81_tendsto_pow d k).const_mul _


lemma L81_smooth_cont (f : smoothFun) : Continuous (f : ℝ → ℝ) :=
  (show ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) from f.2).continuous

lemma L81_fnCalc_add {A : Type*} [CStarAlgebra A] {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (a : A) :
    fnCalc (fun x => f x + g x) a = fnCalc f a + fnCalc g a := by
  unfold fnCalc
  have hf' : Continuous (fun z : ℂ => ((f z.re : ℝ) : ℂ)) := by fun_prop
  have hg' : Continuous (fun z : ℂ => ((g z.re : ℝ) : ℂ)) := by fun_prop
  have := cfc_add (R := ℂ) a (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ))
    hf'.continuousOn hg'.continuousOn
  simpa [Complex.ofReal_add] using this

lemma L81_fnCalc_smul {A : Type*} [CStarAlgebra A] {f : ℝ → ℝ} (hf : Continuous f)
    (r : ℝ) (a : A) :
    fnCalc (fun x => r * f x) a = (r : ℂ) • fnCalc f a := by
  unfold fnCalc
  have hf' : Continuous (fun z : ℂ => ((f z.re : ℝ) : ℂ)) := by fun_prop
  have := cfc_const_mul (R := ℂ) (r : ℂ) (fun z : ℂ => ((f z.re : ℝ) : ℂ)) a hf'.continuousOn
  simpa [Complex.ofReal_mul] using this

/-- The functional `h ↦ Re τ(h(A_F))`. -/
def L81_mu (d : ℕ) : smoothFun →ₗ[ℝ] ℝ where
  toFun h := (tau (fnCalc (h : ℝ → ℝ) (adjFree d))).re
  map_add' f g := by
    have := L81_fnCalc_add (A := L2Free d →L[ℂ] L2Free d) (L81_smooth_cont f) (L81_smooth_cont g)
      (adjFree d)
    show (tau (fnCalc ((f : ℝ → ℝ) + (g : ℝ → ℝ)) (adjFree d))).re = _
    rw [show ((f : ℝ → ℝ) + (g : ℝ → ℝ)) = fun x => (f : ℝ → ℝ) x + (g : ℝ → ℝ) x from rfl, this]
    unfold tau
    simp [inner_add_right]
  map_smul' r f := by
    have := L81_fnCalc_smul (A := L2Free d →L[ℂ] L2Free d) (L81_smooth_cont f) r (adjFree d)
    show (tau (fnCalc (r • (f : ℝ → ℝ)) (adjFree d))).re = _
    rw [show (r • (f : ℝ → ℝ)) = fun x => r * (f : ℝ → ℝ) x from rfl, this]
    unfold tau
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul, Complex.re_ofReal_mul]
    rfl

lemma L81_norm_delta (d : ℕ) : ‖delta (d := d) 1‖ = 1 := by
  simp [delta]

lemma L81_abs_tau_le (d : ℕ) (T : L2Free d →L[ℂ] L2Free d) : |(tau T).re| ≤ ‖T‖ := by
  calc |(tau T).re| ≤ ‖tau T‖ := Complex.abs_re_le_norm _
    _ ≤ ‖delta (d := d) 1‖ * ‖T (delta 1)‖ := by
        unfold tau; exact norm_inner_le_norm _ _
    _ ≤ ‖T‖ := by
        rw [L81_norm_delta, one_mul]
        have := T.le_opNorm (delta (d := d) 1)
        rwa [L81_norm_delta, mul_one] at this

lemma L81_norm_leftReg_le {d : ℕ} (g : FreeGroup (Fin d)) : ‖leftReg g‖ ≤ 1 := by
  unfold leftReg
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma L81_norm_adjFree_le (d : ℕ) : ‖adjFree d‖ ≤ 2 * d := by
  unfold adjFree
  calc ‖∑ i, (sLimit d i + star (sLimit d i))‖ ≤ ∑ i, ‖sLimit d i + star (sLimit d i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖sLimit d i + star (sLimit d i)‖ ≤ ‖sLimit d i‖ + ‖star (sLimit d i)‖ := norm_add_le _ _
          _ ≤ 2 := by
            have h2 : ‖sLimit d i‖ ≤ 1 := L81_norm_leftReg_le (FreeGroup.of i : FreeGroup (Fin d))
            have h3 : ‖star (sLimit d i)‖ = ‖sLimit d i‖ := by
              rw [ContinuousLinearMap.star_eq_adjoint]
              exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _
            linarith
    _ = 2 * d := by simp [mul_comm]

lemma L81_isSelfAdjoint_adjFree (d : ℕ) : IsSelfAdjoint (adjFree d) := by
  unfold adjFree
  exact isSelfAdjoint_sum _ fun i _ => IsSelfAdjoint.add_star_self _

lemma L81_cNorm_zero (f : ℝ → ℝ) (a b : ℝ) :
    cNorm 0 f a b = sSup ((fun x => |f x|) '' Set.Icc a b) := by
  simp [cNorm, supOn]

lemma L81_mu_bound (d : ℕ) (h : smoothFun) :
    |L81_mu d h| ≤ cNorm 0 h (-(2 * d + 1)) (2 * d + 1) := by
  have hc := L81_smooth_cont h
  set K : ℝ := 2 * d + 1 with hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  rw [L81_cNorm_zero]
  set M := sSup ((fun x => |(h : ℝ → ℝ) x|) '' Set.Icc (-K) K) with hM
  have hbdd : BddAbove ((fun x => |(h : ℝ → ℝ) x|) '' Set.Icc (-K) K) :=
    (isCompact_Icc.image (continuous_abs.comp hc)).bddAbove
  have hle : ∀ x ∈ Set.Icc (-K) K, |(h : ℝ → ℝ) x| ≤ M := fun x hx =>
    le_csSup hbdd ⟨x, hx, rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hle 0 ⟨by linarith, hK0⟩)
  refine (L81_abs_tau_le d _).trans ?_
  unfold fnCalc
  apply norm_cfc_le hM0
  intro z hz
  have hz' := (L81_isSelfAdjoint_adjFree d).mem_spectrum_eq_re hz
  have : Nontrivial (L2Free d) := ⟨⟨delta 1, 0, fun h => by
    have := L81_norm_delta d
    rw [h, norm_zero] at this
    exact zero_ne_one this⟩⟩
  have hzn : ‖z‖ ≤ ‖adjFree d‖ := spectrum.norm_le_norm_of_mem hz
  have hre : |z.re| ≤ 2 * d := (Complex.abs_re_le_norm z).trans (hzn.trans (L81_norm_adjFree_le d))
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply hle
  rw [abs_le] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

lemma L81_mu_cs (d : ℕ) : IsCSDistribution (L81_mu d) :=
  ⟨1, 2 * d + 1, 0, one_pos, by positivity, fun f => by
    rw [one_mul]
    exact L81_mu_bound d f⟩

def L81_polyFunLin : ℝ[X] →ₗ[ℝ] smoothFun where
  toFun := polyFun
  map_add' p q := Subtype.ext (funext fun x => by simp [polyFun])
  map_smul' c p := Subtype.ext (funext fun x => by simp [polyFun])

lemma L81_eq_mu (d : ℕ) (ν0 : smoothFun →ₗ[ℝ] ℝ) (hcs : IsCSDistribution ν0)
    (hpoly : ∀ h : ℝ[X], ν0 (polyFun h) = (tau (fnCalc (fun x => h.eval x) (adjFree d))).re) :
    ν0 = L81_mu d := by
  have h1 : ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
      |(ν0.comp L81_polyFunLin) h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K := by
    refine ⟨1, 0, 2 * d + 1, zero_le_one, le_rfl, by positivity, fun q hq h _ => ?_⟩
    rw [Real.rpow_zero, one_mul, one_mul]
    show |ν0 (polyFun h)| ≤ _
    rw [hpoly h]
    exact L81_mu_bound d (polyFun h)
  have h3 := ((tfae_extends_csDistribution (ν0.comp L81_polyFunLin)).out 0 2).mp h1
  refine h3.unique ⟨hcs, fun h => rfl⟩ ⟨L81_mu_cs d, fun h => ?_⟩
  show (tau (fnCalc (fun x => h.eval x) (adjFree d))).re = ν0 (polyFun h)
  exact (hpoly h).symm

lemma L81_expTr (d N : ℕ) (h : ℝ → ℝ) (hh : Continuous h) :
    expTr (L81_P d) N h =
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (fnCalc h (adjPerp σ))) := by
  unfold expTr
  congr 1
  funext σ
  exact L81_trDN_eval d N σ h hh

lemma L81_nu_zero (d : ℕ) (h : ℝ[X]) :
    nu (L81_P d) 0 h = (tau (fnCalc (fun x => h.eval x) (adjFree d))).re := by
  unfold nu
  rw [asympCoeff]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, pow_zero, one_mul]
  have : (fun N : ℕ => expTr (L81_P d) N (fun x => h.eval x)) = fun N : ℕ =>
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (fnCalc (fun x => h.eval x) (adjPerp σ))) := by
    funext N
    exact L81_expTr d N _ h.continuous
  rw [this]
  exact (L81_tendsto_poly d h).limUnder_eq

theorem exists_csDistribution_abs_expTr_adjPerp_sub_le_dev :
    ∃ C : ℝ, ∀ d : ℕ, ∃ ν₁ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution ν₁ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (fnCalc (h : ℝ → ℝ) (adjPerp σ))) -
            (tau (fnCalc (h : ℝ → ℝ) (adjFree d))).re - ν₁ h / N| ≤
          C * (1 + Real.log d) ^ 8 / (N : ℝ) ^ 2 * conjExp β *
            lpNormCircle β (iteratedDeriv 9 (fun θ => (h : ℝ → ℝ) (2 * d * Real.cos θ))) := by
  obtain ⟨C₀, hC₀⟩ := exists_csDistribution_abs_expTr_sub_le
  refine ⟨C₀ * 4 ^ 8, fun d => ?_⟩
  obtain ⟨ν, hν, hbd⟩ := hC₀ (q₀ := 1) (L81_P d) (L81_P_selfAdjoint d) (L81_P_degree d)
  have hν0 : ν 0 = L81_mu d :=
    L81_eq_mu d (ν 0) (hν 0).1 (fun h => by rw [(hν 0).2 h, L81_nu_zero])
  refine ⟨ν 1, (hν 1).1, fun N hN β hβ h => ?_⟩
  have key := hbd N 2 hN le_rfl β hβ h
  rw [L81_expTr d N _ (L81_smooth_cont h), L81_fullNorm] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    div_one, hν0] at key
  have e1 : L81_mu d h = (tau (fnCalc (h : ℝ → ℝ) (adjFree d))).re := rfl
  rw [e1] at key
  have e2 : C₀ * (4 * ((1 : ℕ) : ℝ) * (1 + Real.log d)) ^ (4 * 2) = C₀ * 4 ^ 8 * (1 + Real.log d) ^ 8 := by
    push_cast; ring
  rw [e2] at key
  convert key using 2
  ring

end StrongConv

end

theorem solution : type_of% @StrongConv.exists_csDistribution_abs_expTr_adjPerp_sub_le_dev :=
  @StrongConv.exists_csDistribution_abs_expTr_adjPerp_sub_le_dev
