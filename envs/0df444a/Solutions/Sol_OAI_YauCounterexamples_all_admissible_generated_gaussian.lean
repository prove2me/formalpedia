-- Prove2me | solution 1 for OAI.YauCounterexamples.all_admissible_generated_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:01:11.434994+00:00
-- url     : https://prove2.me/submissions/c2a0c08b-9403-4a1b-aca7-cb1e219f33f2

import Mathlib
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f) (l : List E) :
    ContDiff ℝ ∞ (directionalJet l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih =>
    exact (ih.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const

lemma directionalJet_swap {f : E → F} (hf : ContDiff ℝ ∞ f)
    (a b : E) (l : List E) :
    directionalJet (a :: b :: l) f = directionalJet (b :: a :: l) f := by
  have hg := contDiff_directionalJet hf l
  have hgd := hg.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  ext x
  have ha := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := b))
  have hb := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := a))
  simp only [directionalJet_cons, ha, hb, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  simpa using (hg.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))) a b

lemma directionalJet_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    {l₁ l₂ : List E} (h : l₁.Perm l₂) : directionalJet l₁ f = directionalJet l₂ f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalJet_cons, ih]
  | swap a b l => exact directionalJet_swap hf b a l
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma iteratedFDeriv_eq_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x v = directionalJet (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hd := hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x
    rw [hd.iteratedFDeriv_succ_apply_left', List.ofFn_succ, directionalJet_cons]
    congr 2
    funext y
    exact ih (Fin.tail v) y

theorem smooth_iteratedFDeriv_comp_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) (x : E) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [iteratedFDeriv_eq_directionalJet hf, iteratedFDeriv_eq_directionalJet hf,
    directionalJet_perm hf (σ.ofFn_comp_perm v)]

theorem iteratedFDeriv_finiteTaylorFunction [CompleteSpace F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (finiteTaylorFunction f N) 0 = iteratedFDeriv ℝ k f 0 := by
  classical
  let p : FormalMultilinearSeries ℝ E F := fun j => if j < N then
    (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f 0 else 0
  have hp : HasFiniteFPowerSeriesOnBall (finiteTaylorFunction f N) p 0 N ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk'
    · intro j hj
      simp [p, not_lt.mpr hj]
    · simp
    · intro y _
      simp only [finiteTaylorFunction, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      simp [p, Finset.mem_range.mp hj]
  ext v
  rw [hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  have heq (σ : Equiv.Perm (Fin k)) : p k (fun i => v (σ i)) =
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 v := by
    simp only [p, ite_eq_left hk, smul_apply]
    rw [show (fun i => v (σ i)) = v ∘ σ from rfl,
      smooth_iteratedFDeriv_comp_perm hf]
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero k


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

variable [Fintype σ]

theorem contDiff_realPolyEval (p : MvPolynomial σ ℂ) : ContDiff ℝ ∞ (realPolyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c by funext x; exact realPolyEval_C c x]
    exact contDiff_const
  | add p q hp hq =>
    rw [show realPolyEval (p + q) = fun x => realPolyEval p x + realPolyEval q x by funext x; exact realPolyEval_add p q x]
    exact hp.add hq
  | mul_X p i hp =>
    have hx : ContDiff ℝ ∞ (fun x : σ → ℝ => (x i : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
    rw [show realPolyEval (p * X i) = fun x => realPolyEval p x * (x i : ℂ) by funext x; simp]
    exact hp.mul hx

theorem fderiv_realPolyEval (p : MvPolynomial σ ℂ) (x v : σ → ℝ) :
    fderiv ℝ (realPolyEval p) x v =
      ∑ i, (v i : ℂ) * realPolyEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have heq : realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c := by ext x; exact realPolyEval_C c x
    rw [heq]
    simp
  | add p q hp hq =>
    have h := fderiv_add ((contDiff_realPolyEval p).differentiable (by simp) x)
      ((contDiff_realPolyEval q).differentiable (by simp) x)
    rw [show realPolyEval (p + q) = realPolyEval p + realPolyEval q by ext; simp, h]
    simp only [add_apply, hp, hq, map_add,
      realPolyEval_add, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hcoord : HasFDerivAt (fun x : σ → ℝ => (x j : ℂ))
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply j x)
    rw [show realPolyEval (p * X j) = fun x => realPolyEval p x * (x j : ℂ) by ext; simp,
      fderiv_fun_mul ((contDiff_realPolyEval p).differentiable (by simp) x)
        hcoord.differentiableAt, hcoord.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
      smul_eq_mul, hp, pderiv_mul, realPolyEval_add, realPolyEval_mul, realPolyEval_X,
      pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    have hif (i : σ) : realPolyEval (if j = i then 1 else 0) x =
        if j = i then 1 else 0 := by split_ifs <;> simp
    simp only [hif, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring

theorem fderiv_realPolyEval_eq (p : MvPolynomial σ ℂ) :
    fderiv ℝ (realPolyEval p) =
      ∑ i, realPolyDerivEmbed i ∘ realPolyEval (pderiv i p) := by
  classical
  ext x v
  simp [fderiv_realPolyEval]

theorem realPolyEval_jet_zero_of_coeff (k : ℕ) (p : MvPolynomial σ ℂ)
    (hp : ∀ d : σ →₀ ℕ, d.degree < k + 1 → p.coeff d = 0) :
    iteratedFDeriv ℝ k (realPolyEval p) 0 = 0 := by
  classical
  induction k generalizing p with
  | zero =>
    have h₀ : constantCoeff p = 0 := hp 0 (by simp)
    ext v
    simpa [realPolyEval] using h₀
  | succ k ih =>
    have hp' (i : σ) : ∀ d : σ →₀ ℕ, d.degree < k + 1 → (pderiv i p).coeff d = 0 := by
      intro d hd
      rw [coeff_pderiv, hp (d + Finsupp.single i 1), zero_mul]
      simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hd
    have hz (i : σ) := ih (pderiv i p) (hp' i)
    have hcont (i : σ) : ContDiff ℝ (k : ℕ∞ω)
        (realPolyDerivEmbed i ∘ realPolyEval (pderiv i p)) :=
      ((realPolyDerivEmbed i).contDiff.comp (contDiff_realPolyEval _)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
    have hf : iteratedFDeriv ℝ k (fderiv ℝ (realPolyEval p)) 0 = 0 := by
      rw [fderiv_realPolyEval_eq, iteratedFDeriv_sum_apply (fun i _ => (hcont i).contDiffAt)]
      apply Finset.sum_eq_zero
      intro i _
      rw [(realPolyDerivEmbed i).iteratedFDeriv_comp_left
        (contDiff_realPolyEval _).contDiffAt
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))), hz i]
      ext m v
      simp
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hf, norm_zero]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem realPolyEval_multilinearPolynomial {n : ℕ}
    (B : (σ → ℝ) [×n]→L[ℝ] ℂ) (x : σ → ℝ) :
    realPolyEval (multilinearPolynomial B) x = B (fun _ => x) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hB : B (fun _ => x) = ∑ a : Fin n → σ,
      (∏ i, x (a i)) • B (fun i => Pi.single (a i) 1) := by
    conv_lhs => rw [hx]
    rw [B.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact B.map_smul_univ _ _
  rw [hB]
  simp only [multilinearPolynomial, realPolyEval, map_sum, map_mul, eval_C, map_prod, eval_X]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.real_smul, Complex.ofReal_prod]
  exact mul_comm _ _

theorem realPolyEval_realTaylorPolynomial (f : (σ → ℝ) → ℂ) (N : ℕ) (x : σ → ℝ) :
    realPolyEval (realTaylorPolynomial f N) x = finiteTaylorFunction f N x := by
  simp only [realTaylorPolynomial, realPolyEval, map_sum, map_mul, eval_C,
    finiteTaylorFunction]
  apply Finset.sum_congr rfl
  intro j _
  rw [show MvPolynomial.eval (fun i => (x i : ℂ))
    (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) =
      realPolyEval (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) x from rfl,
    realPolyEval_multilinearPolynomial, Complex.real_smul]
  simp

theorem realTaylorPolynomial_jet {f : (σ → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (realPolyEval (realTaylorPolynomial f N)) 0 =
      iteratedFDeriv ℝ k f 0 := by
  rw [show realPolyEval (realTaylorPolynomial f N) = finiteTaylorFunction f N from
    funext (realPolyEval_realTaylorPolynomial f N)]
  exact iteratedFDeriv_finiteTaylorFunction hf N k hk



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SmoothJetZero
lemma order_zero (f : E → F) : SmoothJetZero f 0 := by intro k hk; omega
lemma add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g N) :
    SmoothJetZero (f + g) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_add_apply (hf.of_le hle).contDiffAt (hg.of_le hle).contDiffAt,
    hfj k hk, hgj k hk, add_zero]
lemma sum {ι : Type*} (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) {N : ℕ}
    (hj : ∀ i ∈ s, SmoothJetZero (f i) N) : SmoothJetZero (∑ i ∈ s, f i) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sum_apply (fun i hi => ((hf i hi).of_le hle).contDiffAt)]
  exact Finset.sum_eq_zero (fun i hi => hj i hi k hk)

lemma mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N M : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g M) :
    SmoothJetZero (fun x => f x * g x) (N + M) := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have hb := norm_iteratedFDeriv_mul_le hf hg (0 : E) hle
  have hz : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f 0‖ * ‖iteratedFDeriv ℝ (k - i) g 0‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ k := by simpa using Finset.mem_range.mp hi
    by_cases h : i < N
    · simp [hfj i h]
    · simp [hgj (k - i) (by omega)]
  rw [hz] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

lemma mul_right {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f : E → A} (hf : ContDiff ℝ ∞ f) (g : E → A) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (h : SmoothJetZero f N) : SmoothJetZero (fun x => f x * g x) N := by
  simpa using h.mul hf hg (order_zero g)

end SmoothJetZero

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
section PolynomialWaves
open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem waveDirectionalDerivative_homogeneous (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) :
    (waveDirectionalDerivative z f).IsHomogeneous (d - 1) := by
  rw [waveDirectionalDerivative_apply]
  apply IsHomogeneous.sum
  intro i _
  simpa only [← C_mul'] using hf.pderiv.C_mul (z i)

theorem waveDirectionalDerivative_degree_zero (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} (hf : f.IsHomogeneous 0) :
    waveDirectionalDerivative z f = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hf
  rw [hf, waveDirectionalDerivative_C]

theorem wavePrimitiveTerm_homogeneous (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : ℓ.IsHomogeneous 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    (wavePrimitiveTerm z ℓ d j f).IsHomogeneous (d + j + 1) := by
  induction d generalizing j f with
  | zero =>
      dsimp [wavePrimitiveTerm]
      have h := ((hℓ.pow (j + 1)).mul hf).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)
      simpa only [one_mul, add_zero, zero_add, C_mul'] using h
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      have h₁ : (ℓ ^ (j + 1) * f).IsHomogeneous (d + 1 + j + 1) := by
        convert (hℓ.pow (j + 1)).mul hf using 1; omega
      have h₂ : (wavePrimitiveTerm z ℓ d (j + 1)
          (waveDirectionalDerivative z f)).IsHomogeneous (d + 1 + j + 1) := by
        convert ih (j + 1) _ hdf using 1; omega
      dsimp only [wavePrimitiveTerm]
      simpa only [C_mul'] using (h₁.sub h₂).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)

theorem wavePrimitiveTerm_derivative (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : waveDirectionalDerivative z ℓ = 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitiveTerm z ℓ d j f) = ℓ ^ j * f := by
  have hj (j : ℕ) : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hpow (j : ℕ) : waveDirectionalDerivative z (ℓ ^ (j + 1)) =
      ((j + 1 : ℕ) : ℂ) • ℓ ^ j := by
    rw [Derivation.leibniz_pow, hℓ, Nat.add_sub_cancel]
    simp [Algebra.smul_def]
  induction d generalizing j f with
  | zero =>
      rw [wavePrimitiveTerm, Derivation.map_smul, Derivation.leibniz,
        waveDirectionalDerivative_degree_zero z hf, hpow]
      simp only [smul_eq_mul, mul_zero, zero_add, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (hj j), one_smul, mul_comm]
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      rw [wavePrimitiveTerm, Derivation.map_smul, map_sub, Derivation.leibniz,
        hpow, ih (j + 1) _ hdf]
      simp only [smul_eq_mul, add_sub_cancel_left]
      rw [mul_smul_comm, smul_smul, inv_mul_cancel₀ (hj j), one_smul, mul_comm]

theorem waveNormSq_pos (z : σ → ℂ) (hz : z ≠ 0) : 0 < waveNormSq z := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (z j))
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

theorem waveLinearCoordinate_homogeneous (z : σ → ℂ) :
    (waveLinearCoordinate z).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [C_mul'] using (isHomogeneous_X ℂ i).C_mul
    (star (z i) / (waveNormSq z : ℂ))

theorem waveLinearCoordinate_derivative (z : σ → ℂ) (hz : z ≠ 0) :
    waveDirectionalDerivative z (waveLinearCoordinate z) = 1 := by
  have hd : (waveNormSq z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (waveNormSq_pos z hz))
  simp only [waveLinearCoordinate, map_sum, Derivation.map_smul,
    waveDirectionalDerivative_X]
  simp only [Algebra.smul_def, algebraMap_eq, ← map_mul, ← map_sum]
  rw [show (1 : MvPolynomial σ ℂ) = C 1 by simp]
  congr 1
  calc
    ∑ i, (star (z i) / (waveNormSq z : ℂ)) * z i =
        (∑ i, z i * star (z i)) / (waveNormSq z : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (waveNormSq z : ℂ) / (waveNormSq z : ℂ) := by
      congr 1
      simp only [Complex.star_def, Complex.mul_conj, waveNormSq, Complex.ofReal_sum]
    _ = 1 := div_self hd

end PolynomialWaves

section CoefficientContinuity
open MvPolynomial
variable {σ X : Type*} [TopologicalSpace X]

namespace CoeffContinuous

theorem const (p : MvPolynomial σ ℂ) : CoeffContinuous (fun _ : X => p) :=
  fun _ => continuous_const

theorem add {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x + G x) := by
  intro m
  convert (hF m).add (hG m) using 1; ext x; simp

theorem neg {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => -F x) := by
  intro m
  convert (hF m).neg using 1; ext x; simp

theorem sub {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem smul {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    {c : X → ℂ} (hc : Continuous c) : CoeffContinuous (fun x => c x • F x) := by
  intro m
  convert hc.mul (hF m) using 1; ext x; simp

theorem mul {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x * G x) := by
  classical
  intro m
  simp only [coeff_mul]
  apply continuous_finsetSum
  intro t _
  exact (hF t.1).mul (hG t.2)

theorem pow {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (n : ℕ) :
    CoeffContinuous (fun x => F x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (X := X) (1 : MvPolynomial σ ℂ)
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem sum {ι : Type*} (s : Finset ι) (F : ι → X → MvPolynomial σ ℂ)
    (hF : ∀ i ∈ s, CoeffContinuous (F i)) :
    CoeffContinuous (fun x => ∑ i ∈ s, F i x) := by
  intro m
  simp only [coeff_sum]
  exact continuous_finsetSum s (fun i hi => hF i hi m)

theorem pderiv {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (i : σ) :
    CoeffContinuous (fun x => pderiv i (F x)) := by
  intro m
  simpa only [coeff_pderiv] using (hF (m + Finsupp.single i 1)).mul_const (m i + 1)

theorem homogeneousComponent {F : X → MvPolynomial σ ℂ}
    (hF : CoeffContinuous F) (N : ℕ) :
    CoeffContinuous (fun x => homogeneousComponent N (F x)) := by
  intro m
  simp only [coeff_homogeneousComponent]
  split_ifs
  · exact hF m
  · exact continuous_const

end CoeffContinuous

variable [Fintype σ]

theorem waveDirectionalDerivative_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => waveDirectionalDerivative (z x) (F x)) := by
  simp only [waveDirectionalDerivative_apply]
  exact CoeffContinuous.sum Finset.univ _ (fun i _ => (hF.pderiv i).smul (hz i))

theorem waveLinearCoordinate_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0) :
    CoeffContinuous (fun x => waveLinearCoordinate (z x)) := by
  have hd : Continuous (fun x => waveNormSq (z x)) := by
    exact continuous_finsetSum Finset.univ (fun i _ => Complex.continuous_normSq.comp (hz i))
  apply CoeffContinuous.sum
  intro i _
  apply (CoeffContinuous.const (MvPolynomial.X i)).smul
  exact (continuous_star.comp (hz i)).div (Complex.continuous_ofReal.comp hd)
    (fun x => by exact_mod_cast (ne_of_gt (waveNormSq_pos (z x) (hz₀ x))))

theorem wavePrimitiveTerm_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (ℓ : X → MvPolynomial σ ℂ)
    (hℓ : CoeffContinuous ℓ) (d j : ℕ) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (ℓ x) d j (F x)) := by
  induction d generalizing j F with
  | zero => exact ((hℓ.pow (j + 1)).mul hF).smul continuous_const
  | succ d ih =>
      exact (((hℓ.pow (j + 1)).mul hF).sub
        (ih (j + 1) _ (waveDirectionalDerivative_coeffContinuous z hz F hF))).smul continuous_const

theorem canonical_wavePrimitive_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (d : ℕ) (F : X → MvPolynomial σ ℂ) (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (waveLinearCoordinate (z x)) d 0 (F x)) :=
  wavePrimitiveTerm_coeffContinuous z hz _ (waveLinearCoordinate_coeffContinuous z hz hz₀) d 0 F hF

end CoefficientContinuity

section FiniteJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

namespace VanishTo

theorem zero (N : ℕ) : VanishTo (0 : MvPolynomial σ R) N := by
  intro m _
  rfl

theorem order_zero (p : MvPolynomial σ R) : VanishTo p 0 := by
  intro m hm
  omega

theorem mono {p : MvPolynomial σ R} {N M : ℕ} (hp : VanishTo p N)
    (h : M ≤ N) : VanishTo p M := fun m hm => hp m (hm.trans_le h)

theorem add {p q : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q N) : VanishTo (p + q) N := by
  intro m hm
  rw [MvPolynomial.coeff_add, hp m hm, hq m hm, add_zero]

theorem sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ R} {N : ℕ}
    (h : ∀ i ∈ s, VanishTo (f i) N) : VanishTo (∑ i ∈ s, f i) N := by
  intro m hm
  simp only [coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => h i hi m hm)

theorem mul {p q : MvPolynomial σ R} {N M : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q M) : VanishTo (p * q) (N + M) := by
  classical
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro t ht
  have ht' : t.1 + t.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
  have hd : t.1.degree + t.2.degree = m.degree := by
    rw [← map_add, ht']
  by_cases h : t.1.degree < N
  · rw [hp t.1 h, zero_mul]
  · have h' : t.2.degree < M := by omega
    rw [hq t.2 h', mul_zero]

theorem mul_left {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (q * p) N := by
  simpa only [zero_add] using (order_zero q).mul hp

theorem mul_right {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (p * q) N := by
  simpa only [add_zero] using hp.mul (order_zero q)

theorem pderiv {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p (N + 1))
    (i : σ) : VanishTo (pderiv i p) N := by
  intro m hm
  rw [coeff_pderiv, hp (m + Finsupp.single i 1), zero_mul]
  simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hm

theorem of_homogeneous {p : MvPolynomial σ R} {N : ℕ} (hp : p.IsHomogeneous N) :
    VanishTo p N := fun _ hm => hp.coeff_eq_zero (ne_of_lt hm)

theorem of_constantCoeff_eq_zero {p : MvPolynomial σ R}
    (hp : constantCoeff p = 0) : VanishTo p 1 := by
  intro m hm
  have h : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
  simpa only [h, constantCoeff_eq] using hp

theorem constantCoeff_eq_zero {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hN : 0 < N) : constantCoeff p = 0 := by
  exact hp 0 (by simpa using hN)

theorem remove_component {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p N) :
    VanishTo (p - homogeneousComponent N p) (N + 1) := by
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = N
  · simp [h]
  · have h' : m.degree < N := by omega
    simp [h, hp m h']

theorem of_constant_and_linear {p : MvPolynomial σ R}
    (h₀ : constantCoeff p = 0) (h₁ : ∀ i, constantCoeff (MvPolynomial.pderiv i p) = 0) :
    VanishTo p 2 := by
  intro m hm
  by_cases hm₀ : m = 0
  · subst m
    exact h₀
  · have hmdeg : m.degree = 1 := by
      have hne : m.degree ≠ 0 := mt (Finsupp.degree_eq_zero_iff m).mp hm₀
      omega
    obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hmdeg
    simpa only [constantCoeff_eq, coeff_pderiv, zero_add, Finsupp.zero_apply,
      Nat.cast_zero, mul_one] using h₁ i

end VanishTo

variable [Fintype σ] [DecidableEq σ]

theorem waveQuadratic_linearization (G : σ → σ → MvPolynomial σ R)
    (u v : σ → MvPolynomial σ R) (z : σ → R) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hu : ∀ i, constantCoeff (u i) = z i) (hv : ∀ i, VanishTo (v i) N) :
    VanishTo (waveQuadratic G (fun i => u i + v i) - waveQuadratic G u -
      2 * ∑ i, C (z i) * v i) (N + 1) := by
  classical
  have hp (i j : σ) : VanishTo
      (G i j * (u i + v i) * (u j + v j) - G i j * u i * u j -
        if i = j then C (z i) * v i + C (z i) * v i else 0) (N + 1) := by
    have hquad : VanishTo (G i j * v i * v j) (N + 1) := by
      exact (((hv i).mul_left (G i j)).mul (hv j)).mono (by omega)
    by_cases hij : i = j
    · subst j
      have hbase : VanishTo (G i i * u i - C (z i)) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hu]
      have hlin : VanishTo ((G i i * u i - C (z i)) * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using hbase.mul (hv i)
      convert (hlin.add hlin).add hquad using 1
      all_goals try with_reducible_and_instances rfl
      simp only [ite_true]
      ring
    · have hg : VanishTo (G i j) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hij]
      have hfirst : VanishTo (G i j * u i * v j) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u i)).mul (hv j)
      have hsecond : VanishTo (G i j * u j * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u j)).mul (hv i)
      convert (hfirst.add hsecond).add hquad using 1
      all_goals try with_reducible_and_instances rfl
      simp only [hij, ite_false]
      ring
  have H := VanishTo.sum Finset.univ (fun i _ =>
    VanishTo.sum Finset.univ (fun j _ => hp i j))
  simpa [waveQuadratic, Finset.sum_sub_distrib, Finset.sum_add_distrib, two_mul] using H

end FiniteJets

section FiniteEikonal
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eikonal_initial_order (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hnull : ∑ i, z i * z i = -1)
    (hcompat : ∀ k, ∑ i, z i * constantCoeff (pderiv k (pderiv i S)) = 0) :
    VanishTo (eikonalResidual G S) 2 := by
  apply VanishTo.of_constant_and_linear
  · simp [eikonalResidual, waveQuadratic, hG, hS, hnull]
  · intro k
    simp [eikonalResidual, waveQuadratic, hG, hdG, hS,
      Finset.sum_add_distrib, mul_comm, hcompat]

theorem eikonal_linearization (G : σ → σ → MvPolynomial σ ℂ)
    (S F : MvPolynomial σ ℂ) (z : σ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (hF : VanishTo F (N + 1)) :
    VanishTo (eikonalResidual G (S + F) - eikonalResidual G S -
      2 * waveDirectionalDerivative z F) (N + 1) := by
  have h := waveQuadratic_linearization G (fun i => pderiv i S)
    (fun i => pderiv i F) z N hN hG hS (hF.pderiv)
  simpa only [eikonalResidual, map_add, add_sub_add_left_eq_sub,
    waveDirectionalDerivative_apply, C_mul'] using h

end FiniteEikonal

section QuadraticSeed
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem wavePhaseSeed_eikonal (G : σ → σ → MvPolynomial σ ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) :
    VanishTo (eikonalResidual G (wavePhaseSeed c z Q)) 2 := by
  apply eikonal_initial_order G _ z hG hdG (wavePhaseSeed_gradient c z Q) hnull
  intro k
  simpa only [wavePhaseSeed_hessian c z Q hQ] using hQz k

end QuadraticSeed

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem wavePrimitive_homogeneous (z : σ → ℂ) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    (wavePrimitive z d p).IsHomogeneous (d + 1) := by
  simpa only [wavePrimitive, zero_add, add_zero] using
    wavePrimitiveTerm_homogeneous z (waveLinearCoordinate z)
      (waveLinearCoordinate_homogeneous z) d 0 p hp

theorem wavePrimitive_derivative (z : σ → ℂ) (hz : z ≠ 0) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitive z d p) = p := by
  simpa only [wavePrimitive, pow_zero, one_mul] using
    wavePrimitiveTerm_derivative z (waveLinearCoordinate z)
      (waveLinearCoordinate_derivative z hz) d 0 p hp

theorem eikonalCorrection_homogeneous (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) (S : MvPolynomial σ ℂ) :
    (eikonalCorrection G z N S).IsHomogeneous (N + 1) := by
  apply wavePrimitive_homogeneous
  simpa only [C_mul'] using
    (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))

variable [DecidableEq σ]

theorem eikonalCorrection_raises (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ) (hN : 1 ≤ N) (S : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hE : VanishTo (eikonalResidual G S) N) :
    VanishTo (eikonalResidual G (S + eikonalCorrection G z N S)) (N + 1) := by
  have hp : (-((2 : ℂ)⁻¹) • homogeneousComponent N (eikonalResidual G S)).IsHomogeneous N := by
    simpa only [C_mul'] using
      (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))
  have hd : 2 * waveDirectionalDerivative z (eikonalCorrection G z N S) =
      -homogeneousComponent N (eikonalResidual G S) := by
    rw [eikonalCorrection, wavePrimitive_derivative z hz N _ hp, two_mul, ← add_smul]
    norm_num
  have hl := eikonal_linearization G S (eikonalCorrection G z N S) z N hN hG hS
    (VanishTo.of_homogeneous (eikonalCorrection_homogeneous G z N S))
  have H := hl.add hE.remove_component
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [hd]
  ring

theorem eikonalIter_spec (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (S₀ : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS₀ : ∀ i, constantCoeff (pderiv i S₀) = z i)
    (hE₀ : VanishTo (eikonalResidual G S₀) 2) (k : ℕ) :
    VanishTo (eikonalIter G z S₀ k - S₀) 3 ∧
    VanishTo (eikonalResidual G (eikonalIter G z S₀ k)) (k + 2) ∧
    (eikonalIter G z S₀ k).totalDegree ≤ max S₀.totalDegree (k + 2) := by
  induction k with
  | zero =>
    exact ⟨by simpa [eikonalIter] using VanishTo.zero (σ := σ) (R := ℂ) 3,
      hE₀, le_max_left _ _⟩
  | succ k ih =>
    obtain ⟨hdiff, hE, hdeg⟩ := ih
    have hS (i : σ) : constantCoeff (pderiv i (eikonalIter G z S₀ k)) = z i := by
      have hd := (hdiff.pderiv i).constantCoeff_eq_zero (by decide)
      rw [map_sub, map_sub] at hd
      exact (sub_eq_zero.mp hd).trans (hS₀ i)
    have hF := eikonalCorrection_homogeneous G z (k + 2) (eikonalIter G z S₀ k)
    refine ⟨?_, ?_, ?_⟩
    · have hv : VanishTo (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k)) 3 :=
        (VanishTo.of_homogeneous hF).mono (by omega)
      convert hdiff.add hv using 1
      all_goals try with_reducible_and_instances rfl
      simp only [eikonalIter]
      ring
    · simpa only [eikonalIter, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using
        eikonalCorrection_raises G z hz (k + 2) (by omega) _ hG hS hE
    · have hfdeg := hF.totalDegree_le
      have hd := totalDegree_add (eikonalIter G z S₀ k)
        (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k))
      simp only [eikonalIter]
      omega

variable {X : Type*} [TopologicalSpace X]

omit [DecidableEq σ] in
theorem eikonalResidual_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (S : X → MvPolynomial σ ℂ)
    (hS : CoeffContinuous S) : CoeffContinuous (fun x => eikonalResidual (G x) (S x)) := by
  apply (CoeffContinuous.const 1).add
  apply CoeffContinuous.sum
  intro i _
  apply CoeffContinuous.sum
  intro j _
  exact ((hG i j).mul (hS.pderiv i)).mul (hS.pderiv j)

omit [DecidableEq σ] in
theorem eikonalIter_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (S₀ : X → MvPolynomial σ ℂ) (hS₀ : CoeffContinuous S₀) (k : ℕ) :
    CoeffContinuous (fun x => eikonalIter (G x) (z x) (S₀ x) k) := by
  induction k with
  | zero => exact hS₀
  | succ k ih =>
    apply ih.add
    apply canonical_wavePrimitive_coeffContinuous z hz hz₀
    exact ((eikonalResidual_coeffContinuous G hG _ ih).homogeneousComponent (k + 2)).smul
      continuous_const



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section ActualEikonal
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem realTaylorPolynomial_constant {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 0 < N) :
    constantCoeff (realTaylorPolynomial f N) = f 0 := by
  have h := realTaylorPolynomial_jet hf N 0 hN
  have hh := congrArg (fun B => B (fun i : Fin 0 => nomatch i)) h
  simpa only [iteratedFDeriv_zero_apply, realPolyEval_at_zero] using hh

theorem realTaylorPolynomial_linear {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 1 < N) (i : σ) :
    constantCoeff (pderiv i (realTaylorPolynomial f N)) =
      fderiv ℝ f 0 (Pi.single i 1) := by
  classical
  have h := realTaylorPolynomial_jet hf N 1 hN
  have hh := congrArg (fun B => B (fun _ => Pi.single i 1)) h
  simpa [iteratedFDeriv_one_apply, fderiv_realPolyEval, Pi.single_apply, apply_ite] using hh

theorem realTaylorPolynomial_remainder {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    SmoothJetZero (f - realPolyEval (realTaylorPolynomial f N)) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sub_apply (hf.of_le hle).contDiffAt
    ((contDiff_realPolyEval _).of_le hle).contDiffAt,
    realTaylorPolynomial_jet hf N k hk, sub_self]

omit [DecidableEq σ] in
theorem VanishTo.realPolyEval {p : MvPolynomial σ ℂ} {N : ℕ} (h : VanishTo p N) :
    SmoothJetZero (YauCounterexamples.realPolyEval p) N := by
  intro k hk
  apply realPolyEval_jet_zero_of_coeff
  exact fun d hd => h d (by omega)

theorem smoothEikonalResidual_jet (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) (N : ℕ)
    (hE : VanishTo (eikonalResidual (fun i j => realTaylorPolynomial (g i j) N) S) N) :
    SmoothJetZero (smoothEikonalResidual g S) N := by
  let G := fun i j => realTaylorPolynomial (g i j) N
  let D : σ → σ → (σ → ℝ) → ℂ := fun i j x =>
    (g i j x - realPolyEval (G i j) x) *
      realPolyEval (pderiv i S) x * realPolyEval (pderiv j S) x
  have hd (i j : σ) : ContDiff ℝ ∞ (D i j) :=
    (((hg i j).sub (contDiff_realPolyEval _)).mul
      (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hdj (i j : σ) : SmoothJetZero (D i j) N :=
    ((realTaylorPolynomial_remainder (hg i j) N).mul_right
      ((hg i j).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)).mul_right
        (((hg i j).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)
  have hc (i : σ) : ContDiff ℝ ∞ (∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun j _ => hd i j))
  have hcs : ContDiff ℝ ∞ (∑ i, ∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun i _ => hc i))
  have hds : SmoothJetZero (∑ i, ∑ j, D i j) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hc i)
      (fun i _ => SmoothJetZero.sum Finset.univ _ (fun j _ => hd i j) (fun j _ => hdj i j))
  have heq : smoothEikonalResidual g S =
      realPolyEval (eikonalResidual G S) + ∑ i, ∑ j, D i j := by
    funext x
    simp only [smoothEikonalResidual, eikonalResidual, waveQuadratic, Pi.add_apply,
      Finset.sum_apply, realPolyEval, map_add, map_one, map_sum, map_mul, D]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hE.realPolyEval.add (contDiff_realPolyEval _)
    hcs hds

end ActualEikonal



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ]

theorem bounded_degree_expansion (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    p = ∑ m ∈ boundedDegreeMonomials (σ:=σ) N, monomial m (p.coeff m) := by
  classical
  conv_lhs => rw [p.as_sum]
  apply Finset.sum_subset
  · intro m hm
    exact (Finsupp.finite_of_degree_le (σ:=σ) N).mem_toFinset.mpr ((le_totalDegree hm).trans hp)
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

theorem realPolyEval_bounded_degree (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    realPolyEval p = fun x => ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
      p.coeff m • realPolyEval (monomial m 1) x := by
  classical
  conv_lhs => rw [bounded_degree_expansion p N hp]
  funext x
  simp [realPolyEval,smul_eq_mul,MvPolynomial.eval_monomial]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_polynomial_jets (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P)
    (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N) (k : ℕ) :
    Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (realPolyEval (P q.1)) q.2) := by
  classical
  have heq (p : X) (x : σ → ℝ) : iteratedFDeriv ℝ k (realPolyEval (P p)) x =
      ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
        (P p).coeff m • iteratedFDeriv ℝ k (realPolyEval (monomial m 1)) x := by
    rw [realPolyEval_bounded_degree (P p) N (hN p),iteratedFDeriv_fun_sum_apply
      (fun m _ => ((contDiff_realPolyEval (monomial m 1)).const_smul _).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)]
    apply Finset.sum_congr rfl
    intro m _
    exact iteratedFDeriv_const_smul_apply'
      ((contDiff_realPolyEval (monomial m 1)).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)
  simp only [heq]
  apply continuous_finsetSum
  intro m _
  exact ((hP m).comp continuous_fst).smul
    (((contDiff_realPolyEval (monomial m 1)).continuous_iteratedFDeriv (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).comp continuous_snd)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_HessianJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_radial_line (F : E → ℝ) (hF : Differentiable ℝ F) (x : E) (t : ℝ) :
    deriv (fun s : ℝ => F (s • x)) t = fderiv ℝ F (t • x) x := by
  simpa only [Function.comp_def, id_eq, one_smul] using ((hF (t • x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const x)).deriv

attribute [local instance] OAI.YauCounterexamples.gaussianDualNorm
attribute [local instance] OAI.YauCounterexamples.gaussianDualSpace
attribute [local instance] OAI.YauCounterexamples.gaussianFormNorm
local instance gaussianFormSpace_r0a5114_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma second_deriv_radial_line (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x : E) (t : ℝ) :
    deriv (deriv (fun s : ℝ => F (s • x))) t =
      fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : deriv (fun s : ℝ => F (s • x)) = fun s => fderiv ℝ F (s • x) x :=
    funext (deriv_radial_line F hd x)
  rw [heq]
  exact (((hD (t • x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const x)).clm_apply (hasDerivAt_const t x)).deriv.trans (by simp)

lemma second_order_line_taylor (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f 1 = f 0 + deriv f 0 + deriv (deriv f) t / 2 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (x₀ := 0) (x := 1) (by norm_num) hf.contDiffOn
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hdf := (hf.differentiable (by norm_num) 0).derivWithin
    (hu 0 (by simp))
  have htw : taylorWithinEval f 1 (uIcc (0 : ℝ) 1) 0 1 = f 0 + deriv f 0 := by
    rw [show 1 = 0+1 from rfl, taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.cast_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, inv_one, sub_zero, zero_add, pow_one, one_mul, one_smul]
    rw [iteratedDerivWithin_one, hdf]
  refine ⟨t, by simpa using ht, ?_⟩
  rw [htw] at he
  norm_num [iteratedDeriv_succ] at he
  linarith

lemma gaussian_of_hessian (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    {r c δ : ℝ} (h0 : F 0 = 0)
    (h1 : ∀ x, fderiv ℝ F 0 x ≤ δ*‖x‖)
    (h2 : ∀ y ∈ Metric.ball (0 : E) r, ∀ v,
      fderiv ℝ (fderiv ℝ F) y v v ≤ -2*c*‖v‖^2)
    {x : E} (hx : x ∈ Metric.ball (0 : E) r) :
    F x ≤ δ*‖x‖-c*‖x‖^2 := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => F (t • x)) :=
    hF.comp (contDiff_id.smul contDiff_const)
  obtain ⟨t,ht,he⟩ := second_order_line_taylor _ hline
  have htx : t • x ∈ Metric.ball (0 : E) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2.le).trans_lt
      (mem_ball_zero_iff.mp hx)
  rw [one_smul, zero_smul, h0, zero_add,
    deriv_radial_line F (hF.differentiable (by norm_num)), zero_smul,
    second_deriv_radial_line F hF] at he
  have hh := h2 (t • x) htx x
  have hl := h1 x
  linarith

omit [NormedSpace ℝ E] in
lemma compact_uniform_value_radius {X B : Type*} [TopologicalSpace X]
    [NormedAddCommGroup B] (H : X × E → B) (hH : Continuous H)
    {P : Set X} (hP : IsCompact P) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ p ∈ P, ∀ y ∈ Metric.ball (0 : E) r,
      ‖H (p,y) - H (p,0)‖ < c := by
  have hH0 : Continuous (fun q : X × E => H (q.1,0)) :=
    hH.comp (continuous_fst.prodMk continuous_const)
  have hopen : IsOpen {q : X × E | ‖H q - H (q.1,0)‖ < c} :=
    isOpen_lt (hH.sub hH0).norm continuous_const
  have hsub : P ×ˢ {(0 : E)} ⊆ {q : X × E | ‖H q - H (q.1,0)‖ < c} := by
    rintro ⟨p,y⟩ ⟨hp,hy⟩
    have hy0 : y = 0 := mem_singleton_iff.mp hy
    subst y
    change ‖H (p,0) - H (p,0)‖ < c
    simpa only [sub_self, norm_zero] using hc
  obtain ⟨u,v,hu,hv,hPu,h0v,huv⟩ := generalized_tube_lemma hP
    isCompact_singleton hopen hsub
  obtain ⟨r,hr,hrv⟩ := Metric.isOpen_iff.mp hv 0 (h0v (mem_singleton 0))
  exact ⟨r,hr,fun p hp y hy => huv ⟨hPu hp,hrv hy⟩⟩

lemma compact_uniform_hessian_radius {X : Type*} [TopologicalSpace X]
    (F : X → E → ℝ)
    (hD : Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (F q.1)) q.2))
    {P : Set X} (hP : IsCompact P) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ p ∈ P, ∀ y ∈ Metric.ball (0 : E) r,
      ‖fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0‖ < c := by
  exact compact_uniform_value_radius _ hD hP hc

theorem compact_gaussian_localization {X : Type*} [TopologicalSpace X]
    (F : X → E → ℝ) (hF : ∀ p, ContDiff ℝ 2 (F p))
    (hD : Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (F q.1)) q.2))
    {P : Set X} (hP : IsCompact P) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ p ∈ P, F p 0 = 0)
    (h1 : ∀ p ∈ P, ∀ x, fderiv ℝ (F p) 0 x ≤ δ p*‖x‖)
    (h2 : ∀ p ∈ P, ∀ v, fderiv ℝ (fderiv ℝ (F p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ P, ∀ x ∈ Metric.ball (0 : E) r,
      F p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  obtain ⟨r,hr,hnear⟩ := compact_uniform_hessian_radius F hD hP hc
  refine ⟨r,hr,fun p hp x hx => gaussian_of_hessian (F p) (hF p) (h0 p hp) (h1 p hp) ?_ hx⟩
  intro y hy v
  have hn := (hnear p hp y hy).le
  have hh := h2 p hp v
  have hb := ((fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0).le_opNorm v)
  have hb' := ((fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v).le_opNorm v
  have hdiff : fderiv ℝ (fderiv ℝ (F p)) y v v - fderiv ℝ (fderiv ℝ (F p)) 0 v v ≤ c*‖v‖^2 := by
    calc
      _ ≤ ‖(fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using le_abs_self
          (fderiv ℝ (fderiv ℝ (F p)) y v v - fderiv ℝ (fderiv ℝ (F p)) 0 v v)
      _ ≤ c*‖v‖^2 := by
        calc
          _ ≤ ‖(fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v‖*‖v‖ := hb'
          _ ≤ (‖fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0‖*‖v‖)*‖v‖ := by gcongr
          _ ≤ (c*‖v‖)*‖v‖ := by gcongr
          _ = c*‖v‖^2 := by ring
  nlinarith [sq_nonneg ‖v‖]

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianFromJet_iterated (f : E → F) (x : E) :
    hessianFromJet (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  change (iteratedFDeriv ℝ 2 f x) (Fin.cons v (fun _ => w)) = _
  simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) f x (Fin.cons v (fun _ => w))

lemma continuous_hessian_of_iterated {X : Type*} [TopologicalSpace X]
    (f : X → E → F)
    (hf : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (f q.1) q.2)) :
    Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (f q.1)) q.2) := by
  simpa only [Function.comp_def, hessianFromJet_iterated] using hessianFromJet.continuous.comp hf

lemma second_fderiv_eval_const (f : E → F) (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  simpa using (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv |> congrArg (fun L => L v)
end SecondJetBridge

section PolynomialSecondJet
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma second_fderiv_realPolyEval (P : MvPolynomial σ ℂ) (x v w : σ → ℝ) :
    fderiv ℝ (fderiv ℝ (realPolyEval P)) x v w =
      ∑ i, ∑ j, (w i : ℂ)*(v j : ℂ)*realPolyEval (pderiv j (pderiv i P)) x := by
  rw [←second_fderiv_eval_const (realPolyEval P)
    ((contDiff_realPolyEval P).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))) x v w]
  simp only [fderiv_realPolyEval]
  rw [fderiv_fun_sum (fun i _ =>
    ((contDiff_const.mul (contDiff_realPolyEval (pderiv i P))).differentiable (by simp) x))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_const_mul ((contDiff_realPolyEval (pderiv i P)).differentiable (by simp) x)]
  simp only [smul_apply, smul_eq_mul, fderiv_realPolyEval,
    Finset.mul_sum, mul_assoc]

lemma polynomial_prescribed_two_jet (P : MvPolynomial σ ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ)
    (hQ : ∀ i j, Q i j = Q j i) (hP : VanishTo (P-wavePhaseSeed c z Q) 3) :
    realPolyEval P 0 = c ∧
    (∀ v, fderiv ℝ (realPolyEval P) 0 v = ∑ i, (v i : ℂ)*z i) ∧
    (∀ v w, fderiv ℝ (fderiv ℝ (realPolyEval P)) 0 v w =
      ∑ i, ∑ j, (w i : ℂ)*(v j : ℂ)*Q j i) := by
  have h0 := hP.constantCoeff_eq_zero (by decide)
  have h1 (i : σ) := (hP.pderiv i).constantCoeff_eq_zero (by decide)
  have h2 (i j : σ) := ((hP.pderiv i).pderiv j).constantCoeff_eq_zero (by decide)
  simp only [map_sub, wavePhaseSeed_constantCoeff] at h0
  simp only [map_sub, wavePhaseSeed_gradient] at h1
  simp only [map_sub, wavePhaseSeed_hessian c z Q hQ] at h2
  refine ⟨by simpa only [realPolyEval_at_zero] using sub_eq_zero.mp h0, ?_, ?_⟩
  · intro v
    simp only [fderiv_realPolyEval, realPolyEval_at_zero, fun i => sub_eq_zero.mp (h1 i)]
  · intro v w
    simp only [second_fderiv_realPolyEval, realPolyEval_at_zero, fun i j => sub_eq_zero.mp (h2 i j)]

end PolynomialSecondJet
section LinearReJet
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

lemma continuous_iterated_re_precomp (f : X → F → ℂ)
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (L : E →L[ℝ] F) (k : ℕ)
    (hj : Continuous (fun q : X × F => iteratedFDeriv ℝ k (f q.1) q.2)) :
    Continuous (fun q : X × E => iteratedFDeriv ℝ k
      (fun x => (f q.1 (L x)).re) q.2) := by
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have heq (p : X) (x : E) : iteratedFDeriv ℝ k (fun y => (f p (L y)).re) x =
      Complex.reCLM.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ k (f p) (L x)).compContinuousLinearMap (fun _ => L)) := by
    change iteratedFDeriv ℝ k (Complex.reCLM ∘ (f p ∘ L)) x = _
    rw [Complex.reCLM.iteratedFDeriv_comp_left ((hf p).comp L.contDiff).contDiffAt hle,
      L.iteratedFDeriv_comp_right (hf p) x hle]
  simp only [heq]
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E) ℂ ℝ)
    Complex.reCLM).continuous.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℂ) (fun _ : Fin k => L)).continuous.comp
      (hj.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))))

lemma first_fderiv_re_precomp (f : F → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x v : E) :
    fderiv ℝ (fun y => (f (L y)).re) x v = (fderiv ℝ f (L x) (L v)).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp x
    ((hf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)
  exact congrArg (fun T => T v) hd.fderiv

lemma second_fderiv_re_precomp (f : F → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f (L y)).re)) x v w =
      (fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w)).re := by
  have hle : (2 : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have he := Complex.reCLM.iteratedFDeriv_comp_left ((hf.comp L.contDiff).contDiffAt) hle
    (x := x)
  rw [L.iteratedFDeriv_comp_right hf x hle] at he
  have hh := congrArg (fun T => T ![v,w]) he
  change (iteratedFDeriv ℝ 2 (Complex.reCLM ∘ f ∘ L) x) ![v,w] =
    ((iteratedFDeriv ℝ 2 f (L x)) (fun i => L (![v,w] i))).re at hh
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_def, Complex.reCLM_apply] using hh

end LinearReJet
variable {E X σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [Fintype σ] [DecidableEq σ]

lemma second_fderiv_sub (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (f-g)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hh := congrArg (hessianFromJet (E := E) (F := ℝ))
    (iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt (i := 2) (x := x))
  simpa only [map_sub, hessianFromJet_iterated] using hh

theorem compact_polynomial_gaussian (L : E →L[ℝ] (σ → ℝ))
    (P : X → MvPolynomial σ ℂ) (hPc : CoeffContinuous P)
    (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    (φ : X → E → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ2 : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (s : X → ℂ) (z : X → σ → ℂ) (Q : X → σ → σ → ℂ)
    (hs0 : ∀ p, (s p).re = φ p 0)
    (hQ : ∀ p i j, Q p i j = Q p j i)
    (hseed : ∀ p, VanishTo (P p-wavePhaseSeed (s p) (z p) (Q p)) 3)
    {K : Set X} (hK : IsCompact K) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (hlinear : ∀ p ∈ K, ∀ v,
      (∑ i, (L v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤ δ p*‖v‖)
    (hgap : ∀ p ∈ K, ∀ v,
      (∑ i, ∑ j, (L v i : ℂ)*(L v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r,
      (realPolyEval (P p) (L x)).re - φ p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  let G := fun p x => (realPolyEval (P p) (L x)).re
  let F := fun p => G p - φ p
  have hle : (2 : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have hG (p : X) : ContDiff ℝ ∞ (G p) :=
    Complex.reCLM.contDiff.comp ((contDiff_realPolyEval (P p)).comp L.contDiff)
  have hF (p : X) : ContDiff ℝ ∞ (F p) := (hG p).sub (hφ p)
  have hGj := continuous_iterated_re_precomp (fun p => realPolyEval (P p))
    (fun p => contDiff_realPolyEval (P p)) L 2 (continuous_polynomial_jets P hPc N hN 2)
  have hFj : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (F q.1) q.2) := by
    have heq (p : X) (x : E) : iteratedFDeriv ℝ 2 (F p) x =
        iteratedFDeriv ℝ 2 (G p) x - iteratedFDeriv ℝ 2 (φ p) x :=
      iteratedFDeriv_sub_apply ((hG p).of_le hle).contDiffAt ((hφ p).of_le hle).contDiffAt
    convert (hGj.sub hφ2) using 1
    all_goals try with_reducible_and_instances rfl
    funext q
    exact heq q.1 q.2
  apply compact_gaussian_localization F (fun p => (hF p).of_le hle)
    (continuous_hessian_of_iterated F hFj) hK δ hc
  · intro p hp
    change (realPolyEval (P p) (L 0)).re - φ p 0 = 0
    rw [map_zero, (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).1,
      hs0 p, sub_self]
  · intro p hp v
    change fderiv ℝ (G p - φ p) 0 v ≤ _
    rw [fderiv_sub ((hG p).differentiable (by simp) 0) ((hφ p).differentiable (by simp) 0)]
    simp only [sub_apply]
    change fderiv ℝ (fun x => (realPolyEval (P p) (L x)).re) 0 v - _ ≤ _
    rw [first_fderiv_re_precomp _ (contDiff_realPolyEval (P p)), map_zero,
      (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).2.1]
    exact hlinear p hp v
  · intro p hp v
    change fderiv ℝ (fderiv ℝ (G p-φ p)) 0 v v ≤ _
    rw [second_fderiv_sub (G p) (φ p) ((hG p).of_le hle) ((hφ p).of_le hle)]
    simp only [sub_apply]
    change fderiv ℝ (fderiv ℝ (fun x => (realPolyEval (P p) (L x)).re)) 0 v v - _ ≤ _
    rw [second_fderiv_re_precomp _ (contDiff_realPolyEval (P p)), map_zero,
      (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).2.2]
    exact hgap p hp v



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PolynomialFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma smoothPhasePolynomial_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    let S := smoothPhasePolynomial g c z Q L
    VanishTo (S - wavePhaseSeed c z Q) 3 ∧
      (∀ i, constantCoeff (pderiv i S) = z i) ∧
      SmoothJetZero (smoothEikonalResidual g S) L ∧
      S.totalDegree ≤ max (wavePhaseSeed c z Q).totalDegree L := by
  let G := fun i j => realTaylorPolynomial (g i j) L
  have hG (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) (by omega)).trans (hg0 i j)
  have hdG (i j l : σ) : constantCoeff (pderiv l (G i j)) = 0 := by
    rw [realTaylorPolynomial_linear (hg i j) (by omega), hdg0 i j]
    rfl
  obtain ⟨hS, hE, hdegree⟩ := eikonalIter_spec G z hz (wavePhaseSeed c z Q) hG
    (wavePhaseSeed_gradient c z Q)
    (wavePhaseSeed_eikonal G c z Q hG hdG hQ hnull hQz) (L - 2)
  have horder : L - 2 + 2 = L := by omega
  rw [horder] at hE hdegree
  refine ⟨hS, ?_, smoothEikonalResidual_jet g hg _ L hE, hdegree⟩
  intro i
  have hd := (hS.pderiv i).constantCoeff_eq_zero (by decide)
  simp only [map_sub, wavePhaseSeed_gradient] at hd
  exact sub_eq_zero.mp hd



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

omit [Fintype σ] in
lemma CoeffContinuous.C {c : X → ℂ} (hc : Continuous c) :
    CoeffContinuous (fun x => MvPolynomial.C (c x) : X → MvPolynomial σ ℂ) := by
  intro m
  simp only [coeff_C]
  split_ifs
  · exact hc
  · exact continuous_const

lemma multilinearPolynomial_coeffContinuous {n : ℕ}
    (B : X → (σ → ℝ) [×n]→L[ℝ] ℂ) (hB : Continuous B) :
    CoeffContinuous (fun x => multilinearPolynomial (B x)) := by
  apply CoeffContinuous.sum Finset.univ
  intro a _
  apply CoeffContinuous.mul _ (CoeffContinuous.const _)
  apply CoeffContinuous.C
  exact hB.eval continuous_const

lemma realTaylorPolynomial_coeffContinuous (f : X → (σ → ℝ) → ℂ) (N : ℕ)
    (hf : ∀ k < N, Continuous (fun p => iteratedFDeriv ℝ k (f p) 0)) :
    CoeffContinuous (fun p => realTaylorPolynomial (f p) N) := by
  apply CoeffContinuous.sum (Finset.range N)
  intro k hk
  exact (CoeffContinuous.const _).mul
    (multilinearPolynomial_coeffContinuous _ (hf k (Finset.mem_range.mp hk)))

lemma wavePhaseSeed_coeffContinuous (c : X → ℂ) (hc : Continuous c)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) :
    CoeffContinuous (fun p => wavePhaseSeed (c p) (z p) (Q p)) := by
  exact ((CoeffContinuous.C hc).add
    (CoeffContinuous.sum Finset.univ _ (fun i _ => (CoeffContinuous.C (hz i)).mul
      (CoeffContinuous.const _)))).add
    ((CoeffContinuous.sum Finset.univ _ (fun i _ => CoeffContinuous.sum Finset.univ _
      (fun j _ => ((CoeffContinuous.C (hQ i j)).mul (CoeffContinuous.const _)).mul
        (CoeffContinuous.const _)))).smul continuous_const)

lemma smoothPhasePolynomial_coeffContinuous (g : X → σ → σ → (σ → ℝ) → ℂ)
    (c : X → ℂ) (hc : Continuous c) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) (L : ℕ)
    (hg : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0)) :
    CoeffContinuous (fun p => smoothPhasePolynomial (g p) (c p) (z p) (Q p) L) :=
  eikonalIter_coeffContinuous _
    (fun i j => realTaylorPolynomial_coeffContinuous _ L (hg i j)) z hz hz₀ _
    (wavePhaseSeed_coeffContinuous c hc z hz Q hQ) (L-2)

omit [DecidableEq σ] in
lemma wavePhaseSeed_degree (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) :
    (wavePhaseSeed c z Q).totalDegree ≤ 2 := by
  unfold wavePhaseSeed
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_smul_le _ _).trans
    apply totalDegree_finsetSum_le
    intro i _
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by
      have h := totalDegree_mul (C (Q i j)) (MvPolynomial.X i)
      simp only [totalDegree_C, totalDegree_X, zero_add] at h ⊢
      omega)

lemma smoothPhasePolynomial_degree (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    (smoothPhasePolynomial g c z Q L).totalDegree ≤ L :=
  (smoothPhasePolynomial_spec g hg hg0 hdg0 c z Q hz hQ hnull hQz L hL).2.2.2.trans
    (max_le ((wavePhaseSeed_degree c z Q).trans hL) le_rfl)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedPhaseGaussian
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E X σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [Fintype σ] [DecidableEq σ]

theorem generated_phase_gaussian (T : E →L[ℝ] (σ → ℝ))
    (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (s : X → ℂ) (hs : Continuous s)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (Q : X → σ → σ → ℂ) (hQ : ∀ p i j, Q p i j = Q p j i)
    (hQc : ∀ i j, Continuous (fun p => Q p i j))
    (hnull : ∀ p, ∑ i, z p i * z p i = -1)
    (hQz : ∀ p k, ∑ i, z p i * Q p k i = 0)
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (φ : X → E → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ2 : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (hs0 : ∀ p, (s p).re = φ p 0)
    {K : Set X} (hK : IsCompact K) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (hlinear : ∀ p ∈ K, ∀ v,
      (∑ i, (T v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤ δ p*‖v‖)
    (hgap : ∀ p ∈ K, ∀ v,
      (∑ i, ∑ j, (T v i : ℂ)*(T v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r,
      (realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) L) (T x)).re -
        φ p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  apply compact_polynomial_gaussian T _
    (smoothPhasePolynomial_coeffContinuous g s hs z hz hz₀ Q hQc L hgj) L
    (fun p => smoothPhasePolynomial_degree (g p) (hg p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hQ p) (hnull p) (hQz p) L hL)
    φ hφ hφ2 s z Q hs0 hQ
    (fun p => (smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hQ p) (hnull p) (hQz p) L hL).1)
    hK δ hc hlinear hgap

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

lemma realQuadratic_sub (a b : ι → ι → ℝ) (v : ι → ℝ) :
    realQuadratic (a-b) v = realQuadratic a v - realQuadratic b v := by
  simp only [realQuadratic, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma phaseFormMatrix_mulVec (U : RealForm (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) (i : ι) :
    (phaseFormMatrix U *ᵥ (fun j => v j)) i = U (EuclideanSpace.basisFun ι ℝ i) v := by
  conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct,
    phaseFormMatrix, EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
lemma realQuadratic_phaseFormMatrix (U : RealForm (EuclideanSpace ℝ ι))
    (v : ι → ℝ) : realQuadratic (phaseFormMatrix U) v =
      U (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have heq : realQuadratic (phaseFormMatrix U) v =
      ∑ i, v i * U (EuclideanSpace.basisFun ι ℝ i) w := by
    unfold realQuadratic
    apply Finset.sum_congr rfl
    intro i _
    rw [← phaseFormMatrix_mulVec U w i]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, w]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  change _ = U w w
  conv_rhs => arg 1; rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, EuclideanSpace.basisFun_repr, w]




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι]

lemma real_phase_quadratic (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (v : EuclideanSpace ℝ ι) :
    (∑ i, ∑ j, (v i : ℂ) * (v j : ℂ) * Q j i).re =
      realQuadratic (Q.map Complex.re) (fun i => v i) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, realQuadratic, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Q j i = Q i j := congrFun (congrFun hQ i) j
  rw [hs]
  ring

lemma phase_squareSum (v : EuclideanSpace ℝ ι) :
    squareSum (fun i => v i) = ‖v‖^2 := by
  simpa only [squareSum, sq] using (EuclideanSpace.real_norm_sq_eq v).symm

lemma phase_matrix_gaussian_gap (H : RealForm PhaseSpace) (z : Fin 3 → ℂ)
    {κ C : ℝ} (Q : ComplexPhaseMatrix) (hQ : PhaseMatrixValid H z κ C Q)
    (v : PhaseSpace) :
    (∑ i, ∑ j, (v i : ℂ) * (v j : ℂ) * Q j i).re - H v v ≤ -4*κ*‖v‖^2 := by
  rw [real_phase_quadratic Q hQ.1]
  have hg := hQ.2.2.2 (fun i => v i)
  erw [phase_squareSum, realQuadratic_sub, realQuadratic_phaseFormMatrix] at hg
  change 4 * κ * ‖v‖ ^ 2 ≤ H v v - realQuadratic (Q.map Complex.re) (fun i => v i) at hg
  linarith

lemma phase_vector_ne_zero (z : ι → ℂ) (hz : ∑ i, z i*z i = -1) : z ≠ 0 := by
  intro he
  simp [he] at hz

lemma phase_matrix_annihilation (Q : Matrix ι ι ℂ) (z : ι → ℂ)
    (h : Q *ᵥ z = 0) (k : ι) : ∑ i, z i * Q k i = 0 := by
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using congrFun h k



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ClosedPhaseMatrixValid
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {X : Type*} [TopologicalSpace X]

lemma isClosed_phaseMatrixValid (H : X → RealForm PhaseSpace) (z : X → Fin 3 → ℂ)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (hz : Continuous z)
    (κ C : ℝ) :
    IsClosed {p : X × ComplexPhaseMatrix | PhaseMatrixValid (H p.1) (z p.1) κ C p.2} := by
  have hs : IsClosed {p : X × ComplexPhaseMatrix | p.2ᵀ = p.2} :=
    isClosed_eq (by fun_prop) continuous_snd
  have ha : IsClosed {p : X × ComplexPhaseMatrix | p.2 *ᵥ z p.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {p : X × ComplexPhaseMatrix | ‖p.2‖ ≤ C} :=
    isClosed_le continuous_snd.norm continuous_const
  have hg : IsClosed {p : X × ComplexPhaseMatrix | ∀ v,
      4*κ*squareSum v ≤ realQuadratic (phaseFormMatrix (H p.1)-p.2.map Complex.re) v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold realQuadratic
    have hM : Continuous (fun p : X × ComplexPhaseMatrix => phaseFormMatrix (H p.1)) :=
      hH.comp continuous_fst
    fun_prop
  exact hs.inter (ha.inter (hb.inter hg))

theorem boundedPhaseSet_isCompact [CompactSpace X]
    (H : X → RealForm PhaseSpace) (hH : Continuous (fun x => phaseFormMatrix (H x)))
    (B κ C : ℝ) : IsCompact (boundedPhaseSet H B κ C) := by
  have hz : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) | ‖p.1.2‖ ≤ B} :=
    isClosed_le (continuous_snd.comp continuous_fst).norm continuous_const
  have hn : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) |
      ∑ i, p.1.2 i * p.1.2 i = -1} := isClosed_eq (by fun_prop) continuous_const
  have hv := isClosed_phaseMatrixValid (fun p : X × (Fin 3 → ℂ) => H p.1)
    (fun p => p.2) (hH.comp continuous_fst) continuous_snd κ C
  have hclosed : IsClosed (boundedPhaseSet H B κ C) := hz.inter (hn.inter hv)
  apply ((isCompact_univ.prod (isCompact_closedBall (0 : Fin 3 → ℂ) B)).prod
    (isCompact_closedBall (0 : ComplexPhaseMatrix) C)).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1⟩,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.2.2.2.1⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma real_phase_linear_general (z : Fin 3 → ℂ) (v : PhaseSpace) :
    (∑ i, (v i : ℂ)*z i).re = inner ℝ v (phaseRealVector z) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, phaseRealVector, mul_comm]

lemma phase_linear_gradient_bound (f : PhaseSpace → ℝ) (z : Fin 3 → ℂ)
    (v : PhaseSpace) :
    (∑ i, (v i : ℂ)*z i).re - fderiv ℝ f 0 v ≤
      ‖phaseRealVector z - gradient f 0‖ * ‖v‖ := by
  rw [real_phase_linear_general, ←inner_gradient_left, real_inner_comm v (gradient f 0),
    ←inner_sub_right]
  simpa only [mul_comm] using real_inner_le_norm v (phaseRealVector z-gradient f 0)

lemma continuous_actualHessianForm {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2)) :
    Continuous (fun p => phaseFormMatrix (actualHessianForm (φ p))) := by
  have hH := (continuous_hessian_of_iterated φ hφ2).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

theorem admissible_generated_gaussian {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (z : X → Fin 3 → ℂ) (hz : Continuous z)
    (Q : X → ComplexPhaseMatrix) (hQ : Continuous Q)
    (hn : ∀ p, ∑ i, z p i*z p i = -1)
    (C : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hv : ∀ p, PhaseMatrixValid (actualHessianForm (φ p)) (z p) κ C (Q p))
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0)) :
    ∃ r > 0, ∀ p, ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
      (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) (z p) (Q p) L) (fun i => x i)).re -
        φ p x ≤ ‖phaseRealVector (z p)-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2 := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  have hsymm : ∀ p, ∀ i j, Q p i j = Q p j i :=
    fun p i j => congrFun (congrFun (hv p).1 j) i
  have hQj : ∀ i j, Continuous (fun p => Q p i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ)
  have hQz : ∀ p, ∀ k, ∑ i, z p i * Q p k i = 0 :=
    fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k
  have hl : ∀ p ∈ (univ : Set X), ∀ v : PhaseSpace,
      (∑ i, (T v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤
        ‖phaseRealVector (z p)-gradient (φ p) 0‖*‖v‖ := by
    intro p _ v
    exact phase_linear_gradient_bound (φ p) (z p) v
  have hgap : ∀ p ∈ (univ : Set X), ∀ v : PhaseSpace,
      (∑ i, ∑ j, (T v i : ℂ)*(T v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*κ*‖v‖^2 := by
    intro p _ v
    exact phase_matrix_gaussian_gap (actualHessianForm (φ p)) (z p) (Q p) (hv p) v
  obtain ⟨r,hr,h⟩ := generated_phase_gaussian (E := PhaseSpace) (X := X) (σ := Fin 3)
    (K := univ) (c := κ) T g hg hg0 hdg0
    (fun p => (φ p 0 : ℂ)) (Complex.continuous_ofReal.comp hφ0)
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q hsymm hQj hn hQz L hL hgj φ hφ hφ2
    (fun _ => rfl) isCompact_univ (fun p => ‖phaseRealVector (z p)-gradient (φ p) 0‖)
    hκ hl hgap
  exact ⟨r,hr,fun p => h p (mem_univ p)⟩

theorem all_admissible_generated_gaussian_oai {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
      (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) (fun i => x i)).re -
        φ p x ≤ ‖phaseRealVector z-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2 := by
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let partition : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hπ : Continuous partition := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (partition p)) (z p) κ C (Q p) := p.property.2.2
  have hgj' : ∀ i j k, k < L → Continuous (fun p : W => iteratedFDeriv ℝ k (g (partition p) i j) 0) := by
    intro i j k hk
    exact (hgj i j k hk).comp hπ
  have hφ2' : Continuous (fun q : W × PhaseSpace => iteratedFDeriv ℝ 2 (φ (partition q.1)) q.2) :=
    hφ2.comp (f := fun q : W × PhaseSpace => (partition q.1,q.2))
      ((hπ.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r,hr,h⟩ := admissible_generated_gaussian
    (fun p : W => g (partition p)) (fun p => hg (partition p)) (fun p => hg0 (partition p))
    (fun p => hdg0 (partition p)) (fun p => φ (partition p)) (fun p => hφ (partition p))
    (hφ0.comp hπ) hφ2' z hz Q hQ hn C hκ hv L hL hgj'
  refine ⟨r,hr,?_⟩
  intro p z Q hz hn hQ x hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ x hx

end YauCounterexamples

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.all_admissible_generated_gaussian_oai.{u_1} := @OAI.YauCounterexamples.all_admissible_generated_gaussian_oai.{u_1}
